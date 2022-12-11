{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ViewPatterns #-}

module InversionOfControl.TcPlugin where

import GHC.Utils.Misc
import Data.Tuple
import GHC.Types.Unique
import Debug.Trace
import Control.Applicative
import Control.Monad
import Data.Functor
import Data.Maybe
import Data.Traversable (for)
import GHC.Builtin.Types
import GHC.Core.Coercion
import GHC.Core.DataCon (DataCon, promoteDataCon)
import GHC.Core.Predicate
import GHC.Core.TyCo.Rep
import GHC.Core.TyCon (TyCon)
import GHC.Core.Type
import GHC.Core.FamInstEnv
import GHC.Data.FastString (fsLit)
import GHC.Driver.Config.Finder (initFinderOpts)
import GHC.Driver.Plugins (Plugin (..), defaultPlugin, purePlugin)
import GHC.Plugins
import GHC.Stack
import GHC.Tc.Plugin
import GHC.Tc.Types
import GHC.Tc.Types.Constraint
import GHC.Tc.Types.Evidence
import GHC.Tc.Instance.Family
import GHC.Types.Name.Occurrence (mkDataOcc, mkTcOcc)
import GHC.Types.Unique.Set
import GHC.Types.Unique.FM
import qualified GHC.Unit.Finder as Finder
import GHC.Unit.Module (mkModuleName)
import GHC.Utils.Outputable (Outputable (..), text, ($$), (<+>))
import Data.IORef
import qualified Data.HashMap.Strict as M

plugin :: Plugin
plugin =
  defaultPlugin
    { tcPlugin = \args -> do
        opts <- foldr id defaultOpts <$> traverse parseArgument args
        return $
          TcPlugin
            { tcPluginInit = lookupExtraDefs
            , tcPluginSolve = solve opts
            , tcPluginRewrite = \_ -> emptyUFM
            , tcPluginStop = const (return ())
            }
    , pluginRecompile = purePlugin
    }
  where
    parseArgument "no_getK_singletonDataCon" = Just (\opts -> opts{getK_singletonDataCon = False})
    parseArgument _ = Nothing
    defaultOpts = Opts{getK_singletonDataCon = True}

data Opts = Opts {getK_singletonDataCon :: Bool}

type ExtractedVal = (Type, Type)

data CachedDict = CachedDict
  { cd_extractedDict :: UniqFM FastString ExtractedVal
  , cd_finishedDict :: UniqFM FastString ExtractedVal
  , cd_unextractedDict :: Type
  , cd_removedKeys :: UniqSet FastString
  }

data CachedDict' = CachedDict'
  { cd_env :: FollowerUFM
  , cd_mut :: IORef CachedDict
  }

data ExtraDefs = ExtraDefs
  { consDC :: DataCon
  , removeDC :: DataCon
  , endDC :: DataCon
  , followTC :: TyCon
  , toConstraintTC :: TyCon
  , getTC :: TyCon
  , defTC :: TyCon
  , typeDictTC :: TyCon
  , cache :: IORef (M.HashMap [Int] CachedDict')
  }

lookupModule :: ModuleName -> FastString -> TcPluginM Module
lookupModule mod_nm _pkg = do
  hsc_env <- getTopEnv
  found_module <- tcPluginIO $ do
    Finder.findPluginModule (hsc_FC hsc_env) (initFinderOpts $ hsc_dflags hsc_env) (hsc_units hsc_env) (hsc_home_unit_maybe hsc_env) mod_nm
  case found_module of
    Found _ h -> return h
    _ -> error "foo"

lookupExtraDefs :: TcPluginM ExtraDefs
lookupExtraDefs = do
  tcPluginTrace "---Plugin init---" (ppr ())
  liftModule <- lookupModule (mkModuleName "InversionOfControl.Lift") (fsLit "inversion-of-control")
  typeDictModule <- lookupModule (mkModuleName "InversionOfControl.TypeDict") (fsLit "inversion-of-control")

  consDC <- tcLookupDataCon =<< lookupOrig typeDictModule (mkDataOcc ":+:")
  removeDC <- tcLookupDataCon =<< lookupOrig typeDictModule (mkDataOcc ":-:")
  endDC <- tcLookupDataCon =<< lookupOrig typeDictModule (mkDataOcc "End")
  toConstraintTC <- tcLookupTyCon =<< lookupOrig typeDictModule (mkTcOcc "ToConstraint")
  getTC <- tcLookupTyCon =<< lookupOrig typeDictModule (mkTcOcc "Get")
  defTC <- tcLookupTyCon =<< lookupOrig typeDictModule (mkTcOcc "Definition")
  followTC <- tcLookupTyCon =<< lookupOrig typeDictModule (mkTcOcc "Follow")
  typeDictTC <- tcLookupTyCon =<< lookupOrig typeDictModule (mkTcOcc "TypeDict")
  cache <- tcPluginIO $ newIORef M.empty

  return ExtraDefs{..}

mkVarSubst :: Ct -> Maybe (TcTyVar, Type)
mkVarSubst ct@(CEqCan{..}) | TyVarLHS tyvar <- cc_lhs = Just (tyvar, cc_rhs)
mkVarSubst _ = Nothing

type FollowerUFM = UniqFM TcTyVar Type

solve :: Opts -> ExtraDefs -> EvBindsVar -> [Ct] -> [Ct] -> TcPluginM TcPluginSolveResult
solve Opts{..} ExtraDefs{..} evBindsVar givens wanteds = do
  famInstEnvs <- unsafeTcPluginTcM tcGetFamInstEnvs

  let consTC = promoteDataCon consDC
  let removeTC = promoteDataCon removeDC
  let endTC = promoteDataCon endDC
  let typeDictT = mkTyConApp typeDictTC []

  let followerUFM0 = listToUFM $ catMaybes $ mkVarSubst <$> givens

  let tryFollow :: UniqFM TyVar Type -> p -> Type -> (Type -> Maybe t) -> (t -> p) -> p
      tryFollow followerUFM stucked x deCon fn = rec x
        where
          rec x =
            case deCon x of
              Just x' -> fn x'
              Nothing -> case getTyVar_maybe x of
                Just var -> case lookupUFM followerUFM var of
                  Just x' -> rec x'
                  Nothing -> stucked
                Nothing -> tryApplyAppTy x []
          tryApplyAppTy x args = case splitAppTy_maybe x of
            Just (x', ty) -> tryApplyAppTy x' (ty : args)
            Nothing -> case getTyVar_maybe x of
              Just var -> case lookupUFM followerUFM var of
                Just x' -> rec (mkAppTys x' args)
                Nothing -> stucked
              Nothing -> stucked
  let idTryFollow followerUFM stucked x deCon = tryFollow followerUFM stucked x deCon id

  let getDictKey :: FollowerUFM -> Type -> TcPluginM (Substitution, Maybe [Int])
      getDictKey followerUFM t =
        idTryFollow followerUFM (return stucked) t $ splitTyConApp_maybe >=> \case
          (tycon, args) | isFamFreeTyCon tycon -> Just do
            args' <- mapM (getDictKey followerUFM) args
            return
              ( Substitution
                  { sub_changeFree = all (sub_changeFree . fst) args'
                  , sub_result = mkTyConApp tycon $ map (sub_result . fst) args'
                  }
              , case mapM snd args' of
                  Nothing -> Nothing
                  Just args'' -> Just $ getKey (getUnique tycon) : concat args''
              )
          _ -> Nothing
        where
          stucked =
            ( Substitution{sub_changeFree = True, sub_result = t}
            , Nothing
            )

  let followFollow :: Type -> Type -> FamInstMatch
      followFollow k t = do
        case lookupFamInstEnv famInstEnvs defTC [k, t] of
          [match] -> match
          matches ->
            error $ "Follow error\n" ++ showPprUnsafe
              ( ppr k
              $$ ppr t
              $$ ppr matches
              $$ ppr famInstEnvs
              )

  let dictFollow :: FollowerUFM -> Type -> TcPluginM (Substitution, Maybe CachedDict')
      dictFollow followerUFM dict = do
        (sub, dictKey) <- getDictKey followerUFM dict
        (sub,) <$>
          case dictKey of
            Nothing -> return Nothing
            Just dictKey' -> Just <$> do
              cache' <- tcPluginIO $ readIORef cache
              case M.lookup dictKey' cache' of
                Just dictRef -> return dictRef
                Nothing -> do
                  let match = followFollow typeDictT (sub_result sub)
                  let inst = fim_instance match
                  let followerUFM = listToUFM $ zip (fi_tvs inst) (fim_tys match)
                  dictRef <- tcPluginIO do
                    newIORef CachedDict
                      { cd_extractedDict = emptyUFM
                      , cd_finishedDict = emptyUFM
                      , cd_unextractedDict = fi_rhs inst
                      , cd_removedKeys = emptyUniqSet
                      }
                  let newDict = CachedDict'{cd_env = followerUFM, cd_mut = dictRef}
                  tcPluginIO do writeIORef cache (M.insert dictKey' newDict cache')
                  return newDict

  let substitute :: FollowerUFM -> FollowerUFM -> Type -> TcPluginM Substitution
      substitute traverseUFM followerUFM t = do
        case splitTyConApp_maybe t of
          Just (tycon, args)
            | tycon == toConstraintTC -> do
                let [dictT] = args

                cd_mut <- tcPluginIO do
                  newIORef CachedDict
                    { cd_extractedDict = emptyUFM
                    , cd_finishedDict = emptyUFM
                    , cd_unextractedDict = dictT
                    , cd_removedKeys = emptyUniqSet
                    }
                let dict = CachedDict'{cd_env = followerUFM, cd_mut = cd_mut}

                extractDict dict
                finishDict dict
                values <- dictValues emptyUniqSet dict

                case values of
                  Just constrs -> do
                    let constr = case map snd constrs of
                          [c] -> c
                          constrs' -> mkTyConApp (cTupleTyCon $ length constrs') constrs'
                    return Substitution{sub_changeFree = False, sub_result = constr}
                  Nothing -> stucked
            | tycon == getTC -> do
                handleGetTC followerUFM args >>= \case
                  Just (key, dict') -> do
                    finishDictElem key dict'
                    (kind, t) <- getFinishedValue key dict'
                    return Substitution{sub_changeFree = False, sub_result = t}
                  Nothing -> do
                    stucked
            | otherwise -> mtraverseType traverseUFM (substitute traverseUFM followerUFM) t
          Nothing -> mtraverseType traverseUFM (substitute traverseUFM followerUFM) t
        where
          stucked = return Substitution{sub_changeFree = True, sub_result = t}

      handleGetTC :: FollowerUFM -> [Type] -> TcPluginM (Maybe (FastString, CachedDict'))
      handleGetTC followerUFM args = do
        let [kind, keyT, dictT] = args
        let goWithKey key = do
              cd_mut <- tcPluginIO do
                newIORef CachedDict
                  { cd_extractedDict = emptyUFM
                  , cd_finishedDict = emptyUFM
                  , cd_unextractedDict = dictT
                  , cd_removedKeys = emptyUniqSet
                  }
              let dict = CachedDict'{cd_env = followerUFM, cd_mut = cd_mut}

              fmap (key,) <$> extractDictUntilKey key dict

        idTryFollow followerUFM (return Nothing) keyT $ \keyT' ->
          (isStrLitTy keyT' >>= \key -> Just do goWithKey key) <|>
          ( splitTyConApp_maybe keyT' >>= \case
              (tycon, args') | tycon == getTC -> Just do
                handleGetTC followerUFM args' >>= \case
                  Nothing -> return Nothing
                  Just (key, dict') -> do
                    finishDictElem key dict'
                    (kindOfKey', key') <- getFinishedValue key dict'
                    case isStrLitTy key' of
                      Nothing -> return Nothing
                      Just key'' -> goWithKey key''
              _ -> Nothing
          )

      extractDictUntilKey :: FastString -> CachedDict' -> TcPluginM (Maybe CachedDict')
      extractDictUntilKey key old'@CachedDict'{cd_env, cd_mut} = rec
        where
          rec = do
            old@(CachedDict dict finished rest removed) <- tcPluginIO $ readIORef cd_mut
            case () of
              _ | key `elemUFM` dict || key `elemUFM` finished -> return $ Just old'
                | key `elementOfUniqSet` removed -> error $ "Get: element removed " ++ showPprUnsafe (ppr key)
                | otherwise -> do
                    let recNewRest rest' = do
                          tcPluginIO $ writeIORef cd_mut old{cd_unextractedDict = rest'}
                          rec
                    let myTryFollow = idTryFollow cd_env (return Nothing)
                    myTryFollow rest $ splitTyConApp_maybe >=> \case
                      (tycon, dargs)
                        | tycon == consTC -> Just do
                            let [_, named, dRest] = dargs
                            myTryFollow named $ splitTyConApp_maybe >=> \case
                              (_, [kind, name, value]) -> Just $
                                myTryFollow name $ isStrLitTy >=> \case
                                  name'
                                    | name' `elementOfUniqSet` removed -> Just $ recNewRest dRest
                                    | otherwise -> Just do
                                        let new = old
                                              { cd_extractedDict = addToUFM dict name' (kind, value)
                                              , cd_unextractedDict = dRest
                                              }
                                        tcPluginIO $ writeIORef cd_mut new
                                        if name' == key
                                          then return $ Just old'
                                          else rec
                              _ -> Nothing
                        | tycon == removeTC -> Just do
                            let [name, rest'] = dargs
                            myTryFollow name $ isStrLitTy >=> \name' -> Just do
                              let new = old
                                    { cd_removedKeys = removed `addOneToUniqSet` name'
                                    , cd_unextractedDict = rest'
                                    }
                              tcPluginIO $ writeIORef cd_mut new
                              when (key == name') $ error $ "Get: element removed " ++ showPprUnsafe (ppr key)
                              rec
                        | tycon == endTC -> Just do
                            return Nothing
                        | tycon == followTC -> Just do
                            let [k, dict2] = dargs
                            (dict2Sub, dict2Data) <- dictFollow cd_env dict2
                            tcPluginIO $ modifyIORef cd_mut $ \old ->
                              old{cd_unextractedDict = mkTyConApp followTC [sub_result dict2Sub]}
                            case dict2Data of
                              Just dict2Data' -> extractDictUntilKey key dict2Data'
                              Nothing -> return Nothing
                        | tycon == getTC -> Just do
                            handleGetTC cd_env dargs >>= \case
                              Just (key, dict') -> do
                                finishDictElem key dict'
                                (kindOfDict'', dict'') <- getFinishedValue key dict'
                                recNewRest dict''
                              Nothing ->
                                return Nothing
                        | otherwise -> Nothing

      finishDictElem :: FastString -> CachedDict' -> TcPluginM ()
      finishDictElem key CachedDict'{cd_env, cd_mut} = do
        d1@(CachedDict dict fdict _ _) <- tcPluginIO (readIORef cd_mut)
        case lookupUFM dict key of
          Nothing -> error $ "finishDictElem key not found " ++ showPprUnsafe (ppr key)
          Just (kind, val) -> do
            val' <- sub_result <$> substitute cd_env cd_env val
            d2@(CachedDict dict2 fdict2 _ _) <- tcPluginIO $ readIORef cd_mut
            when (elemUFM key dict2) do
              let d3 = d2
                    { cd_extractedDict = delFromUFM dict2 key
                    , cd_finishedDict = addToUFM fdict2 key (kind, val')
                    }
              tcPluginIO $ writeIORef cd_mut d3

      getFinishedValue :: FastString -> CachedDict' -> TcPluginM (Type, Type)
      getFinishedValue key CachedDict'{cd_mut} = do
        CachedDict{cd_finishedDict} <- tcPluginIO (readIORef cd_mut)
        case lookupUFM cd_finishedDict key of
          Nothing -> error $ "finishDictElem key not found " ++ showPprUnsafe (ppr key)
          Just (kind, val) -> return (kind, val)

      extractDict ::
        CachedDict' ->
        TcPluginM ()
      extractDict CachedDict'{cd_env, cd_mut} = rec
        where
          rec = do
            old@(CachedDict dict _ rest removed) <- tcPluginIO $ readIORef cd_mut
            let recNewRest rest' = do
                  tcPluginIO $ writeIORef cd_mut old{cd_unextractedDict = rest'}
                  rec
            let myTryFollow = idTryFollow cd_env (return ())
            myTryFollow rest $ splitTyConApp_maybe >=> \case
              (tycon, dargs)
                | tycon == consTC -> Just do
                    let [_, named, dRest] = dargs
                    myTryFollow named $ splitTyConApp_maybe >=> \case
                      (_, [kind, name, value]) -> Just $
                        myTryFollow name $ isStrLitTy >=> \case
                          name'
                            | name' `elementOfUniqSet` removed -> Just $ recNewRest dRest
                            | otherwise -> Just do
                                let new = old
                                      { cd_extractedDict = addToUFM_C const dict name' (kind, value)
                                      , cd_unextractedDict = dRest
                                      }
                                tcPluginIO $ writeIORef cd_mut new
                                rec
                      _ -> Nothing
                | tycon == removeTC -> Just do
                    let [name, rest'] = dargs
                    myTryFollow name $ isStrLitTy >=> \name' -> Just do
                      let new = old
                            { cd_removedKeys = removed `addOneToUniqSet` name'
                            , cd_unextractedDict = rest'
                            }
                      tcPluginIO $ writeIORef cd_mut new
                      rec
                | tycon == endTC -> Just do
                    return ()
                | tycon == followTC -> Just do
                    let [k, dict2] = dargs
                    (dict2Sub, dict2Data) <- dictFollow cd_env dict2
                    tcPluginIO $ modifyIORef cd_mut $ \old ->
                      old{cd_unextractedDict = mkTyConApp followTC [sub_result dict2Sub]}
                    case dict2Data of
                      Just dict2Data' -> extractDict dict2Data'
                      Nothing -> return ()
                | tycon == getTC -> Just do
                    handleGetTC cd_env dargs >>= \case
                      Just (key, dict') -> do
                        finishDictElem key dict'
                        (kindOfDict'', dict'') <- getFinishedValue key dict'
                        recNewRest dict''
                      Nothing -> return ()
                | otherwise -> Nothing

      finishDict ::
        CachedDict' ->
        TcPluginM ()
      finishDict CachedDict'{cd_env, cd_mut} =
        rec =<< tcPluginIO (readIORef cd_mut)
        where
          rec d1@CachedDict{cd_extractedDict = dict, cd_unextractedDict = rest} = do
            case nonDetUFMToList dict of
              ((key, (kind, val)) : _) -> do
                val' <- sub_result <$> substitute cd_env cd_env val
                d2@(CachedDict dict2 fdict2 _ _) <- tcPluginIO $ readIORef cd_mut
                if elemUFM_Directly key dict2
                  then do
                    let d3 = d2
                          { cd_extractedDict = delFromUFM_Directly dict2 key
                          , cd_finishedDict = addToUFM_Directly fdict2 key (kind, val')
                          }
                    tcPluginIO $ writeIORef cd_mut d3
                    rec d3
                  else rec d2
              [] -> do
                idTryFollow cd_env (return ()) rest $ splitTyConApp_maybe >=> \case
                  (tycon, dargs)
                    | tycon == followTC -> Just do
                        let [dict2] = dargs
                        (dict2Sub, dict2Data) <- dictFollow cd_env dict2
                        tcPluginIO $ modifyIORef cd_mut $ \old ->
                          old{cd_unextractedDict = mkTyConApp followTC [sub_result dict2Sub]}
                        case dict2Data of
                          Just dict2Data' -> finishDict dict2Data'
                          Nothing -> return ()
                    | otherwise -> Nothing

      dictValues ::
        UniqSet FastString ->
        CachedDict' ->
        TcPluginM (Maybe [(Type, Type)])
      dictValues removed CachedDict'{cd_env, cd_mut} = do
        CachedDict{..} <- tcPluginIO (readIORef cd_mut)
        let values =
              [ val
              | (key, val) <- nonDetUFMToList cd_finishedDict
              , not $ elemUniqSet_Directly key removed
              ]
        case sizeUFM cd_extractedDict of
          0 ->
            idTryFollow cd_env (return Nothing) cd_unextractedDict $ splitTyConApp_maybe >=> \case
              (tycon, dargs)
                | tycon == endTC -> Just do
                    return $ Just values
                | tycon == followTC -> Just do
                    let [dict2] = dargs
                    (dict2Sub, dict2Data) <- dictFollow cd_env dict2
                    tcPluginIO $ modifyIORef cd_mut $ \old -> old{cd_unextractedDict = sub_result dict2Sub}
                    case dict2Data of
                      Just dict2Data' -> fmap (values ++) <$>
                        dictValues (unionUniqSets removed cd_removedKeys) dict2Data'
                      Nothing -> return Nothing
                | otherwise -> Nothing
          _ -> return Nothing

  let substituteCt (ctPred -> pred) = substitute emptyUFM followerUFM0 pred

  tcPluginTrace "---Plugin givens---" $ ppr ()
  givens' <- mapM substituteCt givens
  tcPluginTrace "---Plugin wanteds---" $ ppr ()
  wanteds' <- mapM substituteCt wanteds

  let pluginCo = mkUnivCo (PluginProv "myplugin") Representational
  newGivens <- for (zip givens' givens) \case
    (Substitution{sub_changeFree = True}, _) -> return Nothing
    (Substitution{sub_result = pred}, ct) ->
      let EvExpr ev = evCast (ctEvExpr $ ctEvidence ct) $ pluginCo (ctPred ct) pred
       in Just . mkNonCanonical <$> newGiven evBindsVar (ctLoc ct) pred ev
  newWanteds <- for (zip wanteds' wanteds) \case
    (Substitution{sub_changeFree = True}, _) -> return Nothing
    (Substitution{sub_result = pred}, ct) -> do
      ev <- GHC.Tc.Plugin.newWanted (ctLoc ct) pred
      return $ Just (mkNonCanonical ev)

  let substEvidence ct ct' = evCast (ctEvExpr $ ctEvidence ct') $ pluginCo (ctPred ct') (ctPred ct)
  let removedGivens = [(substEvidence ct ct', ct) | (Just ct', ct) <- zip newGivens givens]
  let removedWanteds = [(substEvidence ct ct', ct) | (Just ct', ct) <- zip newWanteds wanteds]

  tcPluginTrace "---Plugin solve---" $ ppr givens $$ ppr wanteds
  tcPluginTrace "---Plugin newGivens---" $ ppr newGivens
  tcPluginTrace "---Plugin newWanteds---" $ ppr $ catMaybes newWanteds
  tcPluginTrace "---Plugin removedGivens---" $ ppr removedGivens
  tcPluginTrace "---Plugin removedWanteds---" $ ppr removedWanteds
  return $
    TcPluginOk
      (removedGivens ++ removedWanteds)
      (catMaybes $ newGivens ++ newWanteds)

data Substitution = Substitution
    { sub_changeFree :: Bool
    , sub_result :: Type
    }

mtraverseType :: Monad m =>
  FollowerUFM ->
  (Type -> m Substitution) ->
  Type ->
  m Substitution
mtraverseType followUFM fn = \case
  t | Just t' <- tcView t -> do
    sub <- mtraverseType followUFM fn t'
    return sub
  tv@(TyVarTy v) ->
    case lookupUFM followUFM v of
      Just followed -> mtraverseType followUFM fn followed
      Nothing -> return Substitution
        { sub_changeFree = True
        , sub_result = tv
        }
  (AppTy t1 t2) -> do
    t1' <- fn t1
    t2' <- fn t2
    return Substitution
      { sub_changeFree = sub_changeFree t1' && sub_changeFree t2'
      , sub_result = AppTy (sub_result t1') (sub_result t2')
      }
  (TyConApp tc args) ->
    traverse fn args <&> \args' ->
      Substitution
        { sub_changeFree = all sub_changeFree args'
        , sub_result = TyConApp tc $ map sub_result args'
        }
  t@(ForAllTy _tv _ty) ->
    return
      Substitution
        { sub_changeFree = True
        , sub_result = t
        }
  (FunTy k1 k2 t1 t2) -> do
    t1' <- fn t1
    t2' <- fn t2
    return Substitution
      { sub_changeFree = sub_changeFree t1' && sub_changeFree t2'
      , sub_result = FunTy k1 k2 (sub_result t1') (sub_result t2')
      }
  l@(LitTy _) ->
    return
      Substitution
        { sub_changeFree = True
        , sub_result = l
        }
  (CastTy ty co) -> fn ty <&> \ty' ->
    Substitution
      { sub_changeFree = sub_changeFree ty'
      , sub_result = CastTy (sub_result ty') co
      }
  co@(CoercionTy _) ->
    return
      Substitution
        { sub_changeFree = True
        , sub_result = co
        }

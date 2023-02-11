{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ViewPatterns #-}

module InversionOfControl.TcPlugin where

import Control.Applicative
import Control.Monad
import Control.Monad.Identity
import Data.Functor
import qualified Data.HashMap.Strict as M
import Data.Hashable
import Data.IORef
import Data.Maybe
import Data.Traversable (for)
import Data.Tuple
import Debug.Trace
import GHC.Builtin.Types
import GHC.Core.Coercion
import GHC.Core.DataCon (DataCon, promoteDataCon)
import GHC.Core.FamInstEnv
import GHC.Core.Predicate
import GHC.Core.TyCo.Rep
import GHC.Core.TyCon (TyCon)
import GHC.Core.Type
import GHC.Data.FastString (fsLit)
import GHC.Driver.Config.Finder (initFinderOpts)
import GHC.Driver.Plugins (Plugin (..), defaultPlugin, purePlugin)
import GHC.Generics
import GHC.Plugins
import GHC.Stack
import GHC.Tc.Instance.Family
import GHC.Tc.Plugin
import GHC.Tc.Types
import GHC.Tc.Types.Constraint
import GHC.Tc.Types.Evidence
import GHC.Types.Name.Occurrence (mkDataOcc, mkTcOcc)
import GHC.Types.Unique
import GHC.Types.Unique.FM
import GHC.Types.Unique.Set
import qualified GHC.Unit.Finder as Finder
import GHC.Unit.Module (mkModuleName)
import GHC.Utils.Misc
import GHC.Utils.Outputable (Outputable (..), text, ($$), (<+>))

plugin :: Plugin
plugin =
  defaultPlugin
    { tcPlugin = \args -> do
        opts <- foldr id defaultOpts <$> traverse parseArgument args
        return $
          TcPlugin
            { tcPluginInit = lookupExtraDefs
            , tcPluginSolve = solve opts
            , tcPluginRewrite = const emptyUFM
            , tcPluginStop = const (return ())
            }
    , pluginRecompile = purePlugin
    }
  where
    parseArgument _ = Nothing
    defaultOpts = Opts

data Opts = Opts

type ExtractedVal = (Type, Type)

data CachedDict = CachedDict
  { cd_extractedDict :: UniqFM FastString ExtractedVal
  , cd_finishedDict :: UniqFM FastString ExtractedVal
  , cd_unextractedDict :: Type
  }

data CachedDict' = CachedDict'
  { cd_env :: FollowerUFM
  , cd_mut :: IORef CachedDict
  }

data LiftDict = LiftDict
  { ld_extractedDict :: UniqFM FastString Int
  , ld_unextractedDict :: Type
  , ld_unextractedN :: Int
  }

data LiftDict' = LiftDict'
  { ld_env :: FollowerUFM
  , ld_mut :: IORef LiftDict
  }

data ExtraDefs = ExtraDefs
  { consTC :: TyCon
  , endTC :: TyCon
  , followTC :: TyCon
  , toConstraintTC :: TyCon
  , getTC :: TyCon
  , selfTC :: TyCon
  , defTC :: TyCon
  , typeDictT :: Type
  , cache :: IORef (M.HashMap [DictKeyElem] CachedDict')
  , ld_cache :: IORef (M.HashMap [DictKeyElem] LiftDict')
  , liftsUntilTC :: TyCon
  , succTC :: TyCon
  , zeroT :: Type
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
  endDC <- tcLookupDataCon =<< lookupOrig typeDictModule (mkDataOcc "End")
  toConstraintTC <- tcLookupTyCon =<< lookupOrig typeDictModule (mkTcOcc "ToConstraint")
  getTC <- tcLookupTyCon =<< lookupOrig typeDictModule (mkTcOcc "Get")
  selfTC <- tcLookupTyCon =<< lookupOrig typeDictModule (mkTcOcc "Self")
  defTC <- tcLookupTyCon =<< lookupOrig typeDictModule (mkTcOcc "Definition")
  followTC <- tcLookupTyCon =<< lookupOrig typeDictModule (mkTcOcc "Follow")
  liftsUntilTC <- tcLookupTyCon =<< lookupOrig typeDictModule (mkTcOcc "LiftsUntil")
  typeDictTC <- tcLookupTyCon =<< lookupOrig typeDictModule (mkTcOcc "TypeDict")
  cache <- tcPluginIO $ newIORef M.empty
  ld_cache <- tcPluginIO $ newIORef M.empty
  succDC <- tcLookupDataCon =<< lookupOrig liftModule (mkDataOcc "Succ")
  zeroDC <- tcLookupDataCon =<< lookupOrig liftModule (mkDataOcc "Zero")

  let consTC = promoteDataCon consDC
  let endTC = promoteDataCon endDC
  let succTC = promoteDataCon succDC
  let zeroTC = promoteDataCon zeroDC

  let zeroT = TyConApp zeroTC []
  let typeDictT = TyConApp typeDictTC []

  return ExtraDefs{..}

mkVarSubst :: Ct -> Maybe (TcTyVar, Type)
mkVarSubst ct@(CEqCan{..}) | TyVarLHS tyvar <- cc_lhs = Just (tyvar, cc_rhs)
mkVarSubst _ = Nothing

liftStr :: FastString
liftStr = fsLit "lift"

type FollowerUFM = UniqFM TcTyVar Type

tryFollow :: UniqFM TyVar Type -> (Type -> p) -> Type -> (Type -> Maybe t) -> (t -> p) -> p
tryFollow followerUFM stucked x deCon fn = rec x
  where
    rec x =
      case deCon x of
        Just x' -> fn x'
        Nothing -> case getTyVar_maybe x of
          Just var -> case lookupUFM followerUFM var of
            Just x' -> rec x'
            Nothing -> stucked x
          Nothing -> tryApplyAppTy x []
    tryApplyAppTy x args = case splitAppTy_maybe x of
      Just (x', ty) -> tryApplyAppTy x' (ty : args)
      Nothing -> case getTyVar_maybe x of
        Just var -> case lookupUFM followerUFM var of
          Just x' -> rec (mkAppTys x' args)
          Nothing -> stucked x
        Nothing -> stucked x

idTryFollow :: UniqFM TyVar Type -> (Type -> p) -> Type -> (Type -> Maybe p) -> p
idTryFollow followerUFM stucked x deCon = tryFollow followerUFM stucked x deCon id

data DictKeyElem
  = DictKeyTyCon Int
  | DictKeyVar Int
  | DictKeyLit FastString
  deriving (Eq, Generic, Hashable)

instance Hashable FastString where
  hashWithSalt g str = hashWithSalt g (uniqueOfFS str)
  hash str = hash $ uniqueOfFS str

getDictKey :: FollowerUFM -> Type -> TcPluginM (Substitution, Maybe [DictKeyElem])
getDictKey followerUFM t =
  idTryFollow followerUFM stucked t $ \x ->
    ( splitTyConApp_maybe x >>= \(tycon, args) -> Just do
        args' <- mapM (getDictKey followerUFM) args
        return
          ( Substitution
              { sub_changeFree = all (sub_changeFree . fst) args'
              , sub_result = mkTyConApp tycon $ map (sub_result . fst) args'
              }
          , case mapM snd args' of
              Nothing -> Nothing
              Just args'' -> Just $ DictKeyTyCon (getKey (getUnique tycon)) : concat args''
          )
    )
      <|> ( splitAppTy_maybe x >>= \case
              (x', ty) -> Just do
                args'@[x'', ty'] <- mapM (getDictKey followerUFM) [x', ty]
                return
                  ( Substitution
                      { sub_changeFree = all (sub_changeFree . fst) args'
                      , sub_result = mkAppTys (sub_result $ fst x'') [sub_result $ fst ty']
                      }
                  , case mapM snd args' of
                      Nothing -> Nothing
                      Just args'' -> Just $ concat args''
                  )
          )
  where
    stucked t' = case getTyVar_maybe t' of
      Just var ->
        return
          ( Substitution{sub_changeFree = True, sub_result = t'}
          , Just [DictKeyVar $ getKey (getUnique var)]
          )
      Nothing ->
        case isStrLitTy t' of
          Just str ->
            return
              ( Substitution{sub_changeFree = True, sub_result = t'}
              , Just [DictKeyLit str]
              )
          Nothing -> do
            return
              ( Substitution{sub_changeFree = True, sub_result = t'}
              , Nothing
              )

parseFollowTCArgs :: [Type] -> (Type -> [Type], Type)
parseFollowTCArgs dargs = case dargs of
  [k, dict2] -> (\d -> [k, d], dict2)
  [dict2] -> ((: []), dict2)
  _ -> error $ "followTC: unexpected dargs " ++ showPprUnsafe (ppr dargs)

solve :: Opts -> ExtraDefs -> EvBindsVar -> [Ct] -> [Ct] -> TcPluginM TcPluginSolveResult
solve Opts ExtraDefs{..} evBindsVar givens wanteds = do
  famInstEnvs <- unsafeTcPluginTcM tcGetFamInstEnvs

  let followerUFM0 = listToUFM $ mapMaybe mkVarSubst givens

  let followFollow :: Type -> Type -> Maybe FamInstMatch
      followFollow k t = do
        case lookupFamInstEnv famInstEnvs defTC [k, t] of
          [match] -> Just match
          [] -> Nothing
          matches ->
            error $
              "Follow error\n"
                ++ showPprUnsafe
                  ( ppr k
                      $$ ppr t
                      $$ ppr matches
                      $$ ppr famInstEnvs
                  )

  let dictFollow :: FollowerUFM -> Type -> TcPluginM (Substitution, Maybe CachedDict')
      dictFollow followerUFM dict = do
        (sub, dictKey) <- getDictKey followerUFM dict
        (sub,)
          <$> case dictKey of
            Nothing -> do
              return Nothing
            Just dictKey' -> do
              cache' <- tcPluginIO $ readIORef cache
              case M.lookup dictKey' cache' of
                Just dictRef -> return $ Just dictRef
                Nothing -> case followFollow typeDictT (sub_result sub) of
                  Just match -> do
                    let inst = fim_instance match
                    let followerUFM' = listToUFM $ zip (fi_tvs inst) (fim_tys match)
                    let deself t = case splitTyConApp_maybe t of
                          Just (tycon, []) | tycon == selfTC -> Identity sub
                          _ -> mtraverseType followerUFM' deself t
                    let definition = deself $ fi_rhs inst
                    dictRef <- tcPluginIO do
                      newIORef
                        CachedDict
                          { cd_extractedDict = emptyUFM
                          , cd_finishedDict = emptyUFM
                          , cd_unextractedDict = sub_result $ runIdentity definition
                          }
                    let newDict = CachedDict'{cd_env = followerUFM', cd_mut = dictRef}
                    tcPluginIO do writeIORef cache (M.insert dictKey' newDict cache')
                    return $ Just newDict
                  Nothing -> do
                    return Nothing

  let liftDictFollow :: FollowerUFM -> Type -> TcPluginM (Substitution, Maybe LiftDict')
      liftDictFollow followerUFM dict = do
        (sub, dictKey) <- getDictKey followerUFM dict
        (sub,)
          <$> case dictKey of
            Nothing -> return Nothing
            Just dictKey' -> do
              cache' <- tcPluginIO $ readIORef ld_cache
              case M.lookup dictKey' cache' of
                Just dictRef -> return $ Just dictRef
                Nothing -> case followFollow typeDictT (sub_result sub) of
                  Just match -> do
                    let inst = fim_instance match
                    let followerUFM' = listToUFM $ zip (fi_tvs inst) (fim_tys match)
                    let deself t = case splitTyConApp_maybe t of
                          Just (tycon, []) | tycon == selfTC -> Identity sub
                          _ -> mtraverseType followerUFM' deself t
                    let definition = deself $ fi_rhs inst
                    dictRef <- tcPluginIO do
                      newIORef
                        LiftDict
                          { ld_extractedDict = emptyUFM
                          , ld_unextractedDict = sub_result $ runIdentity definition
                          , ld_unextractedN = 0
                          }
                    let newDict = LiftDict'{ld_env = followerUFM', ld_mut = dictRef}
                    tcPluginIO do writeIORef ld_cache (M.insert dictKey' newDict cache')
                    return $ Just newDict
                  Nothing -> return Nothing

  let substitute :: FollowerUFM -> FollowerUFM -> Type -> TcPluginM Substitution
      substitute traverseUFM followerUFM t = do
        -- tcPluginIO $ putStrLn $ "subBegin\n" ++ showPprUnsafe (ppr t)
        -- ( \sub -> do
        --     tcPluginIO $ putStrLn $ "subEnd\n" ++ showPprUnsafe (ppr t $$ ppr (sub_result sub))
        --     return sub
        --   )
        case splitTyConApp_maybe t of
          Just (tycon, args)
            | tycon == toConstraintTC -> do
                let [dictT] = args

                cd_mut <- tcPluginIO do
                  newIORef
                    CachedDict
                      { cd_extractedDict = emptyUFM
                      , cd_finishedDict = emptyUFM
                      , cd_unextractedDict = dictT
                      }
                let dict = CachedDict'{cd_env = followerUFM, cd_mut = cd_mut}

                extractDict dict
                finishDict dict
                values <- dictValues dict

                case values of
                  Just constrs -> do
                    let constr = case map snd constrs of
                          [c] -> c
                          constrs' -> mkTyConApp (cTupleTyCon $ length constrs') constrs'
                    return Substitution{sub_changeFree = False, sub_result = constr}
                  Nothing -> stucked
            | tycon == getTC -> do
                handleGetTC traverseUFM followerUFM args >>= \case
                  Right (key, dict', otherArgs) -> do
                    finishDictElem key dict'
                    (kind, t) <- getFinishedValue key dict'
                    return
                      Substitution
                        { sub_changeFree = False
                        , sub_result = case otherArgs of
                            [] -> t
                            _ -> mkAppTys t (map sub_result otherArgs)
                        }
                  Left sub -> do
                    return sub
            | tycon == liftsUntilTC -> do
                handleLiftsUntilTC followerUFM args >>= \case
                  Right n -> do
                    let nPean = iterate (\x -> TyConApp succTC [x]) zeroT !! n
                    return Substitution{sub_changeFree = False, sub_result = nPean}
                  Left sub -> return sub
            | otherwise -> mtraverseType traverseUFM (substitute traverseUFM followerUFM) t
          Nothing -> mtraverseType traverseUFM (substitute traverseUFM followerUFM) t
        where
          stucked = mtraverseType traverseUFM (substitute traverseUFM followerUFM) t

      handleGetTC :: FollowerUFM -> FollowerUFM -> [Type] -> TcPluginM (Either Substitution (FastString, CachedDict', [Substitution]))
      handleGetTC traverseUFM followerUFM args = do
        let (kind : keyT : dictT : otherArgs) = args
        let stucked = unchanged (TyConApp getTC args)
        let goWithKey key = do
              cd_mut <- tcPluginIO do
                newIORef
                  CachedDict
                    { cd_extractedDict = emptyUFM
                    , cd_finishedDict = emptyUFM
                    , cd_unextractedDict = dictT
                    }
              let dict = CachedDict'{cd_env = followerUFM, cd_mut = cd_mut}
              let dictTSub = Substitution{sub_result = dictT, sub_changeFree = True}

              otherArgs' <- for otherArgs (substitute traverseUFM followerUFM)
              extractDictUntilKey key dict dictTSub False <&> \case
                Left dictTSub' -> do
                  let otherChangeFree = all sub_changeFree otherArgs'
                  Left
                    Substitution
                      { sub_result = TyConApp getTC (kind : keyT : sub_result dictTSub' : map sub_result otherArgs')
                      , sub_changeFree = sub_changeFree dictTSub' && otherChangeFree
                      }
                Right dict' -> Right (key, dict', otherArgs')

        idTryFollow followerUFM (\_ -> return $ Left stucked) keyT $
          isStrLitTy >=> \key -> Just do goWithKey key

      handleLiftsUntilTC :: FollowerUFM -> [Type] -> TcPluginM (Either Substitution Int)
      handleLiftsUntilTC followerUFM args = do
        let [keyT, dictT] = args
        let stucked = unchanged (TyConApp getTC args)
        let goWithKey key = do
              ld_mut <- tcPluginIO do
                newIORef
                  LiftDict
                    { ld_extractedDict = emptyUFM
                    , ld_unextractedDict = dictT
                    , ld_unextractedN = 0
                    }
              let dict = LiftDict'{ld_env = followerUFM, ld_mut = ld_mut}
              let dictTSub = Substitution{sub_result = dictT, sub_changeFree = True}

              countLiftsUntilKey key dict dictTSub False <&> \case
                Left (0, dictTSub') ->
                  Left dictTSub'{sub_result = TyConApp liftsUntilTC [keyT, sub_result dictTSub']}
                Left (n, Substitution{sub_result}) ->
                  Left
                    Substitution
                      { sub_changeFree = False
                      , sub_result =
                          iterate (\x -> TyConApp succTC [x]) (TyConApp liftsUntilTC [keyT, sub_result]) !! n
                      }
                Right n -> Right n

        idTryFollow followerUFM (\_ -> return $ Left stucked) keyT $
          isStrLitTy >=> \key -> Just do goWithKey key

      countLiftsUntilKey :: FastString -> LiftDict' -> Substitution -> Bool -> TcPluginM (Either (Int, Substitution) Int)
      countLiftsUntilKey key old'@LiftDict'{ld_env, ld_mut} sub followed = rec sub
        where
          rec :: Substitution -> TcPluginM (Either (Int, Substitution) Int)
          rec sub = do
            old@(LiftDict dict rest n) <- tcPluginIO $ readIORef ld_mut
            case lookupUFM dict key of
              Just n' -> return $ Right n'
              Nothing -> do
                let rec' rest'
                      | followed = rec sub
                      | otherwise = rec (changed rest')
                let myTryFollow = idTryFollow ld_env \_ -> return $ Left (0, sub)
                let nsub = if followed then 0 else n
                myTryFollow rest $
                  splitTyConApp_maybe >=> \case
                    (tycon, dargs)
                      | tycon == consTC -> Just do
                          let [_, named, dRest] = dargs
                          myTryFollow named $
                            splitTyConApp_maybe >=> \case
                              (_, [_, name, _]) ->
                                Just do
                                  myTryFollow name $
                                    isStrLitTy >=> \name' ->
                                      Just do
                                        let new =
                                              old
                                                { ld_extractedDict = addToUFM dict name' n
                                                , ld_unextractedDict = dRest
                                                }
                                        case () of
                                          _
                                            | name' == key -> do
                                                tcPluginIO $ writeIORef ld_mut new
                                                return $ Right n
                                            | name' == liftStr -> do
                                                let new' = new{ld_unextractedN = n + 1}
                                                tcPluginIO $ writeIORef ld_mut new'
                                                rec' dRest
                                            | otherwise -> do
                                                tcPluginIO $ writeIORef ld_mut new
                                                rec' dRest
                              _ -> Nothing
                      | tycon == endTC -> Just do
                          error $ "Get: element not found " ++ showPprUnsafe (ppr key)
                      | tycon == followTC -> Just do
                          let (prependKind, dict2) = parseFollowTCArgs dargs
                          dict2Sub0 <- substitute ld_env ld_env dict2
                          (dict2Sub1, dict2Data) <- liftDictFollow ld_env (sub_result dict2Sub0)
                          let dict2Sub = dict2Sub1{sub_changeFree = sub_changeFree dict2Sub1 && sub_changeFree dict2Sub0}
                          let followDict2SubR = TyConApp followTC $ prependKind $ sub_result dict2Sub
                          let sub2 =
                                Substitution
                                  { sub_changeFree = sub_changeFree sub && sub_changeFree dict2Sub && not followed
                                  , sub_result = followDict2SubR
                                  }
                          tcPluginIO $ modifyIORef ld_mut $ \old ->
                            old{ld_unextractedDict = followDict2SubR}
                          case dict2Data of
                            Just dict2Data' ->
                              countLiftsUntilKey key dict2Data' sub2 True >>= \case
                                Left (n2, sub) -> return $ Left (n + n2, sub)
                                Right n2 -> return $ Right $ n + n2
                            Nothing -> return $ Left (n, sub2)
                      | tycon == getTC -> Just do
                          handleGetTC ld_env ld_env dargs >>= \case
                            Right (key, dict', []) -> do
                              finishDictElem key dict'
                              (kindOfDict'', dict'') <- getFinishedValue key dict'
                              tcPluginIO $ writeIORef ld_mut old{ld_unextractedDict = dict''}
                              rec' dict''
                            Left sub' ->
                              Left
                                <$> if sub_changeFree sub'
                                  then return (nsub, sub)
                                  else do
                                    let new = old{ld_unextractedDict = sub_result sub'}
                                    tcPluginIO $ writeIORef ld_mut new
                                    return if followed then (0, sub) else (n, sub')
                      | otherwise -> Nothing

      extractDictUntilKey :: FastString -> CachedDict' -> Substitution -> Bool -> TcPluginM (Either Substitution CachedDict')
      extractDictUntilKey key old'@CachedDict'{cd_env, cd_mut} sub followed = rec sub
        where
          rec sub = do
            old@(CachedDict dict finished rest) <- tcPluginIO $ readIORef cd_mut
            case () of
              _
                | key `elemUFM` dict || key `elemUFM` finished -> return $ Right old'
                | otherwise -> do
                    let sub' rest'
                          | followed = sub
                          | otherwise = changed rest'
                    let myTryFollow = idTryFollow cd_env \_ -> return $ Left sub
                    myTryFollow rest $
                      splitTyConApp_maybe >=> \case
                        (tycon, dargs)
                          | tycon == consTC -> Just do
                              let [_, named, dRest] = dargs
                              myTryFollow named $
                                splitTyConApp_maybe >=> \case
                                  (_, [kind, name, value]) ->
                                    Just do
                                      myTryFollow name $
                                        isStrLitTy >=> \name' ->
                                          Just do
                                            let new =
                                                  old
                                                    { cd_extractedDict = addToUFM dict name' (kind, value)
                                                    , cd_unextractedDict = dRest
                                                    }
                                            tcPluginIO $ writeIORef cd_mut new
                                            if name' == key
                                              then return $ Right old'
                                              else rec $ sub' dRest
                                  _ -> Nothing
                          | tycon == endTC -> Just do
                              error $ "Get: element not found " ++ showPprUnsafe (ppr key)
                          | tycon == followTC -> Just do
                              let (prependKind, dict2) = parseFollowTCArgs dargs
                              dict2Sub0 <- substitute cd_env cd_env dict2
                              (dict2Sub1, dict2Data) <- dictFollow cd_env (sub_result dict2Sub0)
                              let dict2Sub = dict2Sub1{sub_changeFree = sub_changeFree dict2Sub1 && sub_changeFree dict2Sub0}
                              let followDict2SubR = TyConApp followTC $ prependKind $ sub_result dict2Sub
                              let sub2 =
                                    Substitution
                                      { sub_changeFree = sub_changeFree sub && sub_changeFree dict2Sub && not followed
                                      , sub_result = followDict2SubR
                                      }
                              tcPluginIO $ modifyIORef cd_mut $ \old ->
                                old{cd_unextractedDict = followDict2SubR}
                              case dict2Data of
                                Just dict2Data' -> extractDictUntilKey key dict2Data' sub2 True
                                Nothing -> return $ Left sub2
                          | tycon == getTC -> Just do
                              handleGetTC cd_env cd_env dargs >>= \case
                                Right (key, dict', []) -> do
                                  finishDictElem key dict'
                                  (kindOfDict'', dict'') <- getFinishedValue key dict'
                                  tcPluginIO $ writeIORef cd_mut old{cd_unextractedDict = dict''}
                                  rec (sub' dict'')
                                Left sub' ->
                                  Left
                                    <$> if sub_changeFree sub'
                                      then return sub
                                      else do
                                        let new = old{cd_unextractedDict = sub_result sub'}
                                        tcPluginIO $ writeIORef cd_mut new
                                        return if followed then sub else sub'
                          | otherwise -> Nothing

      finishDictElem :: FastString -> CachedDict' -> TcPluginM ()
      finishDictElem key CachedDict'{cd_env, cd_mut} = do
        d1@(CachedDict dict fdict _) <- tcPluginIO (readIORef cd_mut)
        case lookupUFM dict key of
          Nothing ->
            unless (key `elemUFM` fdict) do
              error $ "finishDictElem key not found " ++ showPprUnsafe (ppr key $$ ppr dict)
          Just (kind, val) -> do
            val' <- sub_result <$> substitute cd_env cd_env val
            d2@(CachedDict dict2 fdict2 _) <- tcPluginIO $ readIORef cd_mut
            when (elemUFM key dict2) do
              let d3 =
                    d2
                      { cd_extractedDict = delFromUFM dict2 key
                      , cd_finishedDict = addToUFM fdict2 key (kind, val')
                      }
              tcPluginIO $ writeIORef cd_mut d3

      getFinishedValue :: FastString -> CachedDict' -> TcPluginM (Type, Type)
      getFinishedValue key CachedDict'{cd_mut} = do
        CachedDict{cd_finishedDict} <- tcPluginIO (readIORef cd_mut)
        case lookupUFM cd_finishedDict key of
          Nothing -> error $ "getFinishedDValue key not found " ++ showPprUnsafe (ppr key $$ ppr cd_finishedDict)
          Just (kind, val) -> return (kind, val)

      extractDict ::
        CachedDict' ->
        TcPluginM ()
      extractDict CachedDict'{cd_env, cd_mut} = rec
        where
          rec = do
            old@(CachedDict dict _ rest) <- tcPluginIO $ readIORef cd_mut
            let recNewRest rest' = do
                  tcPluginIO $ writeIORef cd_mut old{cd_unextractedDict = rest'}
                  rec
            let myTryFollow = idTryFollow cd_env (\_ -> return ())
            myTryFollow rest $
              splitTyConApp_maybe >=> \case
                (tycon, dargs)
                  | tycon == consTC -> Just do
                      let [_, named, dRest] = dargs
                      myTryFollow named $
                        splitTyConApp_maybe >=> \case
                          (_, [kind, name, value]) ->
                            Just $
                              myTryFollow name $
                                isStrLitTy >=> \name' -> Just do
                                  let new =
                                        old
                                          { cd_extractedDict = addToUFM_C const dict name' (kind, value)
                                          , cd_unextractedDict = dRest
                                          }
                                  tcPluginIO $ writeIORef cd_mut new
                                  rec
                          _ -> Nothing
                  | tycon == endTC -> Just do
                      return ()
                  | tycon == followTC -> Just do
                      let (prependKind, dict2) = parseFollowTCArgs dargs
                      dict2Sub0 <- substitute cd_env cd_env dict2
                      (dict2Sub1, dict2Data) <- dictFollow cd_env (sub_result dict2Sub0)
                      let dict2Sub = dict2Sub1{sub_changeFree = sub_changeFree dict2Sub1 && sub_changeFree dict2Sub0}
                      tcPluginIO $ modifyIORef cd_mut $ \old ->
                        old{cd_unextractedDict = TyConApp followTC $ prependKind $ sub_result dict2Sub}
                      forM_ dict2Data extractDict
                  | tycon == getTC -> Just do
                      handleGetTC cd_env cd_env dargs >>= \case
                        Right (key, dict', []) -> do
                          finishDictElem key dict'
                          (kindOfDict'', dict'') <- getFinishedValue key dict'
                          recNewRest dict''
                        Left sub' -> do
                          let new = old{cd_unextractedDict = sub_result sub'}
                          tcPluginIO $ writeIORef cd_mut new
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
                d2@(CachedDict dict2 fdict2 _) <- tcPluginIO $ readIORef cd_mut
                if elemUFM_Directly key dict2
                  then do
                    let d3 =
                          d2
                            { cd_extractedDict = delFromUFM_Directly dict2 key
                            , cd_finishedDict = addToUFM_Directly fdict2 key (kind, val')
                            }
                    tcPluginIO $ writeIORef cd_mut d3
                    rec d3
                  else rec d2
              [] -> do
                idTryFollow cd_env (\_ -> return ()) rest $
                  splitTyConApp_maybe >=> \case
                    (tycon, dargs)
                      | tycon == followTC -> Just do
                          let (prependKind, dict2) = parseFollowTCArgs dargs
                          dict2Sub0 <- substitute cd_env cd_env dict2
                          (dict2Sub1, dict2Data) <- dictFollow cd_env (sub_result dict2Sub0)
                          let dict2Sub = dict2Sub1{sub_changeFree = sub_changeFree dict2Sub1 && sub_changeFree dict2Sub0}
                          tcPluginIO $ modifyIORef cd_mut $ \old ->
                            old{cd_unextractedDict = mkTyConApp followTC $ prependKind $ sub_result dict2Sub}
                          forM_ dict2Data finishDict
                      | otherwise -> Nothing

      dictValues ::
        CachedDict' ->
        TcPluginM (Maybe [(Type, Type)])
      dictValues CachedDict'{cd_env, cd_mut} = do
        CachedDict{..} <- tcPluginIO (readIORef cd_mut)
        let values = map snd $ nonDetUFMToList cd_finishedDict
        case sizeUFM cd_extractedDict of
          0 ->
            idTryFollow cd_env (\_ -> return Nothing) cd_unextractedDict $
              splitTyConApp_maybe >=> \case
                (tycon, dargs)
                  | tycon == endTC -> Just do
                      return $ Just values
                  | tycon == followTC -> Just do
                      let (prependKind, dict2) = parseFollowTCArgs dargs
                      dict2Sub0 <- substitute cd_env cd_env dict2
                      (dict2Sub1, dict2Data) <- dictFollow cd_env (sub_result dict2Sub0)
                      let dict2Sub = dict2Sub1{sub_changeFree = sub_changeFree dict2Sub1 && sub_changeFree dict2Sub0}
                      tcPluginIO $ modifyIORef cd_mut $ \old ->
                        old{cd_unextractedDict = mkTyConApp followTC $ prependKind $ sub_result dict2Sub}
                      case dict2Data of
                        Just dict2Data' -> fmap (values ++) <$> dictValues dict2Data'
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
unchanged :: Type -> Substitution
unchanged t = Substitution{sub_changeFree = True, sub_result = t}

changed :: Type -> Substitution
changed t = Substitution{sub_changeFree = False, sub_result = t}

mtraverseType ::
  Monad m =>
  FollowerUFM ->
  (Type -> m Substitution) ->
  Type ->
  m Substitution
mtraverseType followUFM fn = \case
  t | Just t' <- tcView t -> do
    mtraverseType followUFM fn t'
  tv@(TyVarTy v) ->
    case lookupUFM followUFM v of
      Just followed -> mtraverseType followUFM fn followed
      Nothing ->
        return
          Substitution
            { sub_changeFree = True
            , sub_result = tv
            }
  (AppTy t1 t2) -> do
    t1' <- fn t1
    t2' <- fn t2
    return
      Substitution
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
    return
      Substitution
        { sub_changeFree = sub_changeFree t1' && sub_changeFree t2'
        , sub_result = FunTy k1 k2 (sub_result t1') (sub_result t2')
        }
  l@(LitTy _) ->
    return
      Substitution
        { sub_changeFree = True
        , sub_result = l
        }
  (CastTy ty co) ->
    fn ty <&> \ty' ->
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

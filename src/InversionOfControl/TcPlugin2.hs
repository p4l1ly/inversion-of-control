{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ViewPatterns #-}

module InversionOfControl.TcPlugin2 where

import GHC.Types.Unique
import Debug.Trace
import Control.Applicative (Alternative ((<|>)))
import Control.Monad (guard, (>=>))
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

data ExtraDefs = ExtraDefs
  { getkFam :: TyCon
  , getFam :: TyCon
  , incFam :: TyCon
  , kTyCon :: TyCon
  , kDataCon :: DataCon
  , peanTyCon :: TyCon
  , zeroDataCon :: DataCon
  , dConsDataCon :: DataCon
  , dEndDataCon :: DataCon
  , dLiftFam :: TyCon
  , dToConstraintFam :: TyCon
  , typedictTyCon :: TyCon
  , dRemoveFam :: TyCon
  , dToConstraintCachedFam :: TyCon
  , dScopeFam :: TyCon
  , dKArg :: TyCon
  , dDictDefFam :: TyCon
  , cache :: IORef (M.HashMap [Int] (IORef CachedDict))
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

  getkFam <- tcLookupTyCon =<< lookupOrig typeDictModule (mkTcOcc "GetK")
  getFam <- tcLookupTyCon =<< lookupOrig typeDictModule (mkTcOcc "Get")
  incFam <- tcLookupTyCon =<< lookupOrig liftModule (mkTcOcc "Inc")
  kTyCon <- tcLookupTyCon =<< lookupOrig liftModule (mkTcOcc "K")
  kDataCon <- tcLookupDataCon =<< lookupOrig liftModule (mkDataOcc "K")
  peanTyCon <- tcLookupTyCon =<< lookupOrig liftModule (mkTcOcc "Pean")
  zeroDataCon <- tcLookupDataCon =<< lookupOrig liftModule (mkDataOcc "Zero")
  dConsDataCon <- tcLookupDataCon =<< lookupOrig typeDictModule (mkDataOcc ":+:")
  dEndDataCon <- tcLookupDataCon =<< lookupOrig typeDictModule (mkDataOcc "End")
  dLiftFam <- tcLookupTyCon =<< lookupOrig typeDictModule (mkTcOcc "LiftTags")
  dToConstraintFam <- tcLookupTyCon =<< lookupOrig typeDictModule (mkTcOcc "ToConstraint")
  typedictTyCon <- tcLookupTyCon =<< lookupOrig typeDictModule (mkTcOcc "TypeDict")
  dRemoveFam <- tcLookupTyCon =<< lookupOrig typeDictModule (mkTcOcc "Remove")
  cache <- tcPluginIO $ newIORef M.empty

  dKArg <- tcLookupTyCon =<< lookupOrig typeDictModule (mkTcOcc "KArg")
  dToConstraintCachedFam <- tcLookupTyCon =<< lookupOrig typeDictModule (mkTcOcc "ToConstraintCached")
  dScopeFam <- tcLookupTyCon =<< lookupOrig typeDictModule (mkTcOcc "Scope")
  dDictDefFam <- tcLookupTyCon =<< lookupOrig typeDictModule (mkTcOcc "DictDef")

  return ExtraDefs{..}

mkVarSubst :: Ct -> Maybe (TcTyVar, Type)
mkVarSubst ct@(CEqCan{..}) | TyVarLHS tyvar <- cc_lhs = Just (tyvar, cc_rhs)
mkVarSubst _ = Nothing

solve :: Opts -> ExtraDefs -> EvBindsVar -> [Ct] -> [Ct] -> TcPluginM TcPluginSolveResult
solve Opts{..} ExtraDefs{..} evBindsVar givens wanteds = do
  famInstEnvs <- unsafeTcPluginTcM tcGetFamInstEnvs
  let headTyCon = fst . fromJust . splitTyConApp_maybe . head . fi_tys
  let dictDefs = listToUFM $ map (\x -> (headTyCon x, famInstRHS x)) $ familyInstances famInstEnvs dDictDefFam
  tcPluginTrace "dictDefs" (ppr dictDefs)

  let endTyCon = promoteDataCon dEndDataCon
  let consTyCon = promoteDataCon dConsDataCon
  let kPromTyCon = promoteDataCon kDataCon
  let zeroTyCon = promoteDataCon zeroDataCon
  let isK t = case tyConAppTyCon_maybe t of
        Nothing -> False
        Just tHead -> eqType (mkTyConTy tHead) (mkTyConTy (promoteDataCon kDataCon))
  let substUFM = listToUFM $ catMaybes $ mkVarSubst <$> givens

  let tryFollow stucked x' deCon fn = rec x'
        where
          rec x' =
            case deCon x' of
              Just x'' -> fn x''
              Nothing -> case getTyVar_maybe x' of
                Just var -> case lookupUFM substUFM var of
                  Just x'' -> rec x''
                  Nothing -> stucked
                Nothing -> stucked
  let idTryFollow stucked x' deCon = tryFollow stucked x' deCon id

  let withCache ::
        [Int] ->
        TyCon ->
        ([Int] -> IORef CachedDict -> TcPluginM a) ->
        (IORef CachedDict -> a -> TcPluginM b) ->
        TcPluginM b
      withCache scope dictTyCon go0 go = do
        cache' <- tcPluginIO $ readIORef cache
        let dictId = getKey $ getUnique dictTyCon
        let newDict =
              CachedDict
                { cd_extractedDict = emptyUFM
                , cd_finishedDict = emptyUFM
                , cd_unextractedDict =
                    fromMaybe (error $ "DictDef not found " ++ showPprUnsafe (ppr dictTyCon $$ ppr dictDefs)) $
                      lookupUFM dictDefs dictTyCon
                , cd_removedKeys = emptyUniqSet
                }
        if null scope
          then do
            dictRef <- case M.lookup [dictId] cache' of
              Nothing -> do
                tcPluginIO do
                  dictRef <- newIORef newDict
                  writeIORef cache (M.insert [dictId] dictRef cache')
                  return dictRef
              Just dictRef -> return dictRef
            go0 [] dictRef >>= go dictRef
          else do
            case M.lookup (dictId : scope) cache' of
              Nothing -> do
                dictRef1 <- case M.lookup [dictId] cache' of
                  Nothing -> do
                    tcPluginIO do
                      dictRef <- newIORef newDict
                      writeIORef cache (M.insert [dictId] dictRef cache')
                      return dictRef
                  Just dictRef -> return dictRef
                go0 [] dictRef1
                dictRef2 <- tcPluginIO do readIORef dictRef1 >>= newIORef
                go0 scope dictRef2 >>= go dictRef2
              Just dictRef -> do
                go0 scope dictRef >>= go dictRef

  let substitute :: [Int] -> Type -> TcPluginM Substitution
      substitute scope t = do
        let ufmForFollow = if null scope then emptyUFM else substUFM -- follow variables only if scope is present
        case splitTyConApp_maybe t of
          Just (tycon, args)
              -- TODO: Get, GetK, Follow, Lift
              | tycon == dToConstraintCachedFam -> do
                  let [constr] = args
                  tryFollow'' scope constr descend $ splitTyConApp_maybe >=> \case
                    (constrTyCon, []) -> Just do
                      withCache scope constrTyCon
                        (\sc dr -> extractDict sc dr >> finishDict sc dr)
                        \dictRef _ -> do
                          CachedDict{cd_finishedDict, cd_unextractedDict} <- tcPluginIO $ readIORef dictRef
                          idTryFollow (return Nothing) cd_unextractedDict $ splitTyConApp_maybe >=> \case
                            (tycon, []) | tycon == endTyCon -> Just do
                              let constrs = nonDetEltsUFM cd_finishedDict
                              case map snd constrs of
                                [c] -> return $ Just c
                                constrs' -> do
                                  let arity = length constrs'
                                  return $ Just $ mkTyConApp (cTupleTyCon arity) constrs'
                            _ -> Nothing
                    _ -> Nothing
              | tycon == dScopeFam -> do
                  let [k, scopeType, block] = args
                  let stucked = Substitution
                        { sub_tyFamFree = False
                        , sub_changeFree = True
                        , sub_result = t
                        }
                  tryFollow'' scope scopeType stucked $ splitTyConApp_maybe >=>
                    \(scopeTyCon, args) ->
                      case args of
                        [] | scopeTyCon `elemUFM` dictDefs -> Just do
                          block' <- substitute (getKey (getUnique scopeTyCon) : scope) block
                          if sub_tyFamFree block'
                            then return block'{sub_changeFree = False}
                            else return Substitution
                              { sub_tyFamFree = False
                              , sub_changeFree = sub_changeFree block'
                              , sub_result = mkTyConApp dScopeFam [k, scopeType, sub_result block']
                              }
                        _ -> Nothing
              -- | tycon == dKArg -> do
              --     case scope of
              --       [] -> return Nothing
              --       _ -> do
              --         let [k, key] = args
              --         tryFollow' key Nothing isStrLitTy \key' -> do
              --           cache' <- tcPluginIO $ readIORef cache
              --           let newDict = (emptyUFM, fromJust $ lookupUFM dictDefs defsTyCon', emptyUniqSet)
              --           let dict = lookupWithDefaultUFM cache' newDict defsTyCon'
              --           defs@(defsDict, defsRest, _) <- extractDict dict  -- TODO laziness: extractDictUntil
              --           let cache'' = addToUFM cache' defsTyCon' defs
              --           tcPluginIO $ writeIORef cache cache''
              --           case lookupUFM defsDict key' of
              --             Nothing -> 
              --               case splitTyConApp_maybe defsRest of
              --                 Just (tycon, []) | tycon == endTyCon ->
              --                   error $ "key not present in defs " ++ showPprUnsafe (ppr key' $$ ppr defsDict)
              --                 _ -> return Nothing
              --             Just (kind, val) -> substitute defsTyCon val <&> (<|> Just val)
              | otherwise -> mtraverseType ufmForFollow (substitute scope) t
          Nothing -> mtraverseType ufmForFollow (substitute scope) t
      extractDict ::
        [Int] ->
        IORef CachedDict ->
        TcPluginM ()
      extractDict scope dictRef = rec
        where
          rec = do
            old@(CachedDict dict _ rest removed) <- tcPluginIO $ readIORef dictRef
            let recNewRest rest' = do
                  tcPluginIO $ writeIORef dictRef old{cd_unextractedDict = rest'}
                  rec
            let myTryFollow = idTryFollow (subAndGo scope recNewRest () rest)
            myTryFollow rest $ splitTyConApp_maybe >=> \case
              (tycon, dargs)
                | tycon == consTyCon -> Just do
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
                                tcPluginIO $ writeIORef dictRef new
                                rec
                      _ -> Nothing
                | tycon == dRemoveFam -> Just do
                    let [name, rest'] = dargs
                    myTryFollow name $ isStrLitTy >=> \name' -> Just do
                      let new = old{cd_removedKeys = removed `addOneToUniqSet` name'}
                      tcPluginIO $ writeIORef dictRef new
                      rec
                | tycon == endTyCon -> Just do
                    return ()
                | otherwise -> Nothing

      finishDict ::
        [Int] ->
        IORef CachedDict ->
        TcPluginM ()
      finishDict scope dictRef =
        rec =<< tcPluginIO (readIORef dictRef)
        where
          rec d1@(CachedDict dict _ _ _) = do
            case nonDetUFMToList dict of
              ((key, (kind, val)) : _) -> do
                val' <- fromMaybe val <$> substitute scope val
                d2@(CachedDict dict2 fdict2 _ _) <- tcPluginIO $ readIORef dictRef
                if elemUFM_Directly key dict2
                  then do
                    let d3 = d2
                          { cd_extractedDict = delFromUFM_Directly dict2 key
                          , cd_finishedDict = addToUFM_Directly fdict2 key (kind, val')
                          }
                    tcPluginIO $ writeIORef dictRef d3
                    rec d3
                  else rec d2
              [] -> return ()

      subAndGo :: [Int] -> (Type -> TcPluginM b) -> b -> Type -> TcPluginM b
      subAndGo scope fn old x =
        substitute scope x >>= \case
          Nothing -> return old
          Just rest' -> fn rest'

      tryFollow' :: [Int] -> Type -> b -> (Type -> Maybe a) -> (a -> TcPluginM b) -> TcPluginM b
      tryFollow' scope x b deCon fn =
        tryFollow (subAndGo scope (\x' -> tryFollow' scope x' b deCon fn) b x) x deCon fn

      tryFollow'' :: [Int] -> Type -> b -> (Type -> Maybe (TcPluginM b)) -> TcPluginM b
      tryFollow'' scope x b fn = tryFollow' scope x b fn id

  let substituteCt (ctPred -> pred) = substitute [] pred

  tcPluginTrace "---Plugin givens---" $ ppr ()
  givens' <- mapM substituteCt givens
  tcPluginTrace "---Plugin wanteds---" $ ppr ()
  wanteds' <- mapM substituteCt wanteds

  let pluginCo = mkUnivCo (PluginProv "myplugin") Representational
  newGivens <- for (zip givens' givens) \case
    (Nothing, _) -> return Nothing
    (Just pred, ct) ->
      let EvExpr ev = evCast (ctEvExpr $ ctEvidence ct) $ pluginCo (ctPred ct) pred
       in Just . mkNonCanonical <$> newGiven evBindsVar (ctLoc ct) pred ev
  newWanteds <- for (zip wanteds' wanteds) \case
    (Nothing, _) -> return Nothing
    (Just pred, ct) -> do
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
    { sub_tyFamFree :: Bool
    , sub_changeFree :: Bool
    , sub_result :: Type
    }

mtraverseType :: Applicative m =>
  UniqFM TcTyVar Type ->
  (Type -> m Substitution) ->
  Type ->
  m Substitution
mtraverseType followUFM fn = \case
  t | Just t' <- tcView t -> do
    sub <- mtraverseType followUFM fn t'
    return sub{sub_tyFamFree = False}
  tv@(TyVarTy v) ->
    case lookupUFM followUFM v of
      Just followed -> mtraverseType followUFM fn followed
      Nothing -> return Substitution
        { sub_tyFamFree = False
        , sub_changeFree = True
        , sub_result = tv
        }
  (AppTy t1 t2) -> do
    t1' <- fn t1
    t2' <- fn t2
    return Substitution
      { sub_tyFamFree = sub_tyFamFree t1' && sub_tyFamFree t2'
      , sub_changeFree = sub_changeFree t1' && sub_changeFree t2'
      , sub_result = AppTy (sub_result t1') (sub_result t2')
      }
  (TyConApp tc args) ->
    traverse fn args <&> \args' ->
      Substitution
        { sub_tyFamFree = all sub_tyFamFree args' && isFamFreeTyCon tc
        , sub_changeFree = all sub_changeFree args'
        , sub_result = TyConApp tc $ map sub_result args'
        }
  t@(ForAllTy _tv _ty) ->
    return
      Substitution
        { sub_tyFamFree = False
        , sub_changeFree = True
        , sub_result = t
        }
  (FunTy k1 k2 t1 t2) -> do
    t1' <- fn t1
    t2' <- fn t2
    return Substitution
      { sub_tyFamFree = sub_tyFamFree t1' && sub_tyFamFree t2'
      , sub_changeFree = sub_changeFree t1' && sub_changeFree t2'
      , sub_result = FunTy k1 k2 (sub_result t1') (sub_result t2')
      }
  l@(LitTy _) ->
    return
      Substitution
        { sub_tyFamFree = True
        , sub_changeFree = True
        , sub_result = l
        }
  (CastTy ty co) -> fn ty <&> \ty' ->
    Substitution
      { sub_tyFamFree = sub_tyFamFree ty'
      , sub_changeFree = sub_changeFree ty'
      , sub_result = CastTy (sub_result ty') co
      }
  co@(CoercionTy _) ->
    return
      Substitution
        { sub_tyFamFree = False
        , sub_changeFree = True
        , sub_result = co
        }

data TypeDictCon = Cons | End | Lift deriving (Show)
instance Outputable TypeDictCon where
  ppr End = "End"
  ppr Cons = "Cons"
  ppr Lift = "Lift"

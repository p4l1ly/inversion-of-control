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

import Debug.Trace
import Control.Applicative (Alternative ((<|>)))
import Control.Monad (guard)
import Data.Functor
import qualified Data.Map as M
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
  , dKArg :: TyCon
  , dDictDefFam :: TyCon
  , cache :: IORef (UniqFM TyCon (UniqFM FastString Type, Type))
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
  let cache = emptyUFM

  dKArg <- tcLookupTyCon =<< lookupOrig typeDictModule (mkTcOcc "KArg")
  dToConstraintCachedFam <- tcLookupTyCon =<< lookupOrig typeDictModule (mkTcOcc "ToConstraintCached")
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

  let reduce :: Bool -> Type -> TcPluginM (Maybe Type)
      reduce eqK t = tryFollow (return Nothing) t splitTyConApp_maybe \(tycon, args) -> case () of
        _
          | tycon == getkFam -> do
              let [sym, d] = args
              tryFollow (return Nothing) sym isStrLitTy \key -> do
                let lookupTypeDict :: Bool -> Bool -> Type -> TcPluginM (Maybe Type)
                    lookupTypeDict top again dRec = tryFollow' dRec splitTyConApp_maybe \case
                      (tycon, dargs)
                        | tycon == endTyCon ->
                            return $ Just $ anyTypeOfKind (mkTyConApp kTyCon [])
                        | tycon == dLiftFam -> do
                            let [dRest] = dargs
                            fmap (mkTyConApp incFam . (:[])) <$> lookupTypeDict False True dRest
                        | tycon == consTyCon ->
                            let kind : named : dRest : kindArgs = dargs
                             in tryFollow' named splitTyConApp_maybe \(_, (_ : sym' : value : _)) ->
                                  tryFollow' sym' isStrLitTy \case
                                    key'
                                      | key == key' ->
                                          tryFollow' kind tyConAppTyCon_maybe \case
                                            kindTyCon
                                              | kindTyCon == kTyCon -> return $ Just value
                                              | otherwise -> error "GetK: expected K kind"
                                      | otherwise -> lookupTypeDict False True dRest
                        | again ->
                            reduce False dRec >>= \case
                              Nothing -> return Nothing
                              Just dRec' -> lookupTypeDict top False dRec'
                        | otherwise -> return Nothing
                      where
                        tryFollow' =
                          tryFollow if top
                            then return Nothing
                            else return $ Just (mkTyConApp getkFam [sym, dRec])
                lookupTypeDict True True d >>= \case
                  Nothing -> return Nothing
                  Just dsub -> do
                    dsub' <- reduce False dsub
                    tcPluginTrace "---Plugin dsub---" $ ppr sym $$ ppr d $$ ppr dsub $$ ppr dsub'
                    -- TODO unless eqK, replace with K n t and create eqK
                    return $ dsub' <|> Just dsub
          | tycon == getFam -> do
              let kind0 : sym : d : kind0Args = args
              tryFollow (return Nothing) sym isStrLitTy \key -> do
                let lookupTypeDict :: Bool -> Bool -> Type -> TcPluginM (Maybe Type)
                    lookupTypeDict top again dRec = tryFollow' dRec splitTyConApp_maybe \case
                      (tycon, dargs)
                        | tycon == endTyCon ->
                            return $ Just $ mkAppTys (anyTypeOfKind kind0) kind0Args
                        | tycon == dLiftFam ->
                            let [dRest] = dargs
                             in lookupTypeDict False True dRest
                        | tycon == consTyCon ->
                            let kind : named : dRest : kindArgs = dargs
                             in tryFollow' named splitTyConApp_maybe \(_, (kind1 : sym' : value : kind1Args)) ->
                                  tryFollow' sym' isStrLitTy \case
                                    key'
                                      | key == key' -> return $ Just $ mkAppTys value kind0Args
                                      | otherwise -> lookupTypeDict False True dRest
                        | again ->
                            reduce False dRec >>= \case
                              Nothing -> return Nothing
                              Just dRec' -> lookupTypeDict top False dRec'
                        | otherwise -> return Nothing
                      where
                        tryFollow' =
                          tryFollow if top
                            then return Nothing
                            else return $ Just (mkTyConApp getFam (kind0 : sym : dRec : kind0Args))
                lookupTypeDict True True d >>= \case
                  Nothing -> return Nothing
                  Just dsub -> do
                    dsub' <- reduce False dsub
                    tcPluginTrace "---Plugin dsub2---" $ ppr sym $$ ppr d $$ ppr dsub $$ ppr dsub'
                    return $ dsub' <|> Just dsub
          | tycon == dToConstraintFam -> do
              tcPluginTrace "---Plugin toConstraint---" $ ppr t
              let descend :: [Type] -> Type -> UniqSet FastString -> TcPluginM (Maybe [Type])
                  descend result dRec removed = tryFollow' dRec splitTyConApp_maybe \case
                    (tycon, dargs)
                      | tycon == endTyCon -> return $ Just result
                      | tycon == consTyCon ->
                          let [_, named, dRest] = dargs
                           in tryFollow' named splitTyConApp_maybe \case
                                (_, [kind, name, value]) ->
                                  tryFollow' name isStrLitTy \name' -> case () of
                                    _ | name' `elementOfUniqSet` removed ->
                                          descend result dRest removed
                                      | tcIsConstraintKind kind ->
                                          reduce False value >>= \case
                                            Nothing -> descend (value : result) dRest removed
                                            Just value' -> descend (value' : result) dRest removed
                                      | otherwise ->
                                          tryFollow' kind tyConAppTyCon_maybe \case
                                            kindTyCon
                                              | kindTyCon == typedictTyCon ->
                                                  descend result value emptyUniqSet >>= \case
                                                    Nothing -> descend (mkTyConApp dToConstraintFam [value] : result) dRest removed
                                                    Just result' -> descend result' dRest removed
                                              | otherwise -> do
                                                  tcPluginTrace "---Plugin toConstraint Err1---" $ ppr kindTyCon $$ ppr kind $$ ppr name $$ ppr value
                                                  error "ToConstraint: expected Constraint or TypeDict kind"
                      | tycon == dRemoveFam -> do
                          let [name, dRest] = dargs
                          tryFollow' name isStrLitTy \name' ->
                            descend result dRest (removed `addOneToUniqSet` name')
                      | otherwise -> return $ Nothing <|> Nothing
                    where
                      tryFollow' = tryFollow case result of
                        [] -> return Nothing
                        _ -> return $ Just $ mkTyConApp dToConstraintFam [dRec] : result

              descend [] (head args) emptyUniqSet >>= \case
                Just constrs -> do
                  -- trace ("constrs " ++ showPprUnsafe (ppr constrs)) $ return ()
                  tcPluginTrace "---Plugin toConstraint constrs---" $ ppr args $$ ppr constrs
                  case constrs of
                    [c] -> return $ Just c
                    _ -> do
                      let arity = length constrs
                      return $ Just $ mkTyConApp (cTupleTyCon arity) constrs
                Nothing -> return Nothing
          | tycon == dToConstraintCachedFam -> do
              let [constr, defs] = args
              tryFollow (return Nothing) constr splitTyConApp_maybe \(constrTyCon, []) ->
                tryFollow (return Nothing) defs splitTyConApp_maybe \(defsTyCon, []) -> do
                  cache' <- tcPluginIO $ readIORef cache
                  let (constrDict, constrRest) = lookupWithDefaultUFM cache' (emptyUFM, fromJust $ lookupUFM dictDefs constrTyCon) constrTyCon
                  let (defsDict, defsRest) = lookupWithDefaultUFM cache' (emptyUFM, fromJust $ lookupUFM dictDefs defsTyCon) defsTyCon
                  let descend :: (UniqFM TyCon Type, Type, UniqSet FastString) -> TcPluginM (UniqFM TyCon Type, Type, UniqSet FastString)
                      descend old@(dict, rest, removed) = tryFollow (return old) rest splitTyConApp_maybe \case
                        (tycon, dargs)
                          | tycon == endTyCon -> return old
                          -- | tycon == consTyCon ->
                          --     let [_, named, dRest] = dargs
                          --     in tryFollow (return old) named splitTyConApp_maybe \case
                          --           (_, [kind, name, value]) ->
                          --             tryFollow (return old) name isStrLitTy \name' -> case () of
                          --               _ | name' `elementOfUniqSet` removed ->
                          --                     descend result dRest removed
                          --                 | tcIsConstraintKind kind ->
                          --                     reduce False value >>= \case
                          --                       Nothing -> descend (value : result) dRest removed
                          --                       Just value' -> descend (value' : result) dRest removed
                          --                 | otherwise ->
                          --                     tryFollow (return old) kind tyConAppTyCon_maybe \case
                          --                       kindTyCon
                          --                         | kindTyCon == typedictTyCon ->
                          --                             descend result value emptyUniqSet >>= \case
                          --                               Nothing -> descend (mkTyConApp dToConstraintFam [value] : result) dRest removed
                          --                               Just result' -> descend result' dRest removed
                          --                         | otherwise -> do
                          --                             tcPluginTrace "---Plugin toConstraint Err1---" $ ppr kindTyCon $$ ppr kind $$ ppr name $$ ppr value
                          --                             error "ToConstraint: expected Constraint or TypeDict kind"
                          | tycon == dRemoveFam -> do
                              let [name, rest'] = dargs
                              tryFollow (return old) name isStrLitTy \name' ->
                                descend (result dRest (removed `addOneToUniqSet` name')
                          -- | otherwise -> return $ Nothing <|> Nothing
                  -- descend constrRest
                  let constrs = nonDetEltsUFM constrDict
                  undefined
              undefined
          | otherwise -> mtraverseType (reduce False) t

  let reduceCt (ctPred -> pred) =
        case classifyPredType pred of
          EqPred NomEq t1 t2 -> do
            r1 <- reduce (isK t2) t1
            r2 <- reduce (isK t1) t2
            if isNothing r1 && isNothing r2
              then return Nothing
              else return $ Just $ mkPrimEqPred (fromMaybe t1 r1) (fromMaybe t2 r2)
          _ -> reduce False pred

  tcPluginTrace "---Plugin givens---" $ ppr ()
  givens' <- mapM reduceCt givens
  -- tcPluginTrace "---Plugin deriveds---" $ ppr ()
  -- deriveds' <- mapM reduceCt deriveds
  tcPluginTrace "---Plugin wanteds---" $ ppr ()
  wanteds' <- mapM reduceCt wanteds

  let pluginCo = mkUnivCo (PluginProv "myplugin") Representational
  newGivens <- for (zip givens' givens) \case
    (Nothing, _) -> return Nothing
    (Just pred, ct) ->
      let EvExpr ev = evCast (ctEvExpr $ ctEvidence ct) $ pluginCo (ctPred ct) pred
       in Just . mkNonCanonical <$> newGiven evBindsVar (ctLoc ct) pred ev
  -- newDeriveds <- for (zip deriveds' deriveds) \case
  --   (Nothing, _) -> return Nothing
  --   (Just pred, ct) -> Just . mkNonCanonical <$> GHC.TcPluginM.Extra.newDerived (ctLoc ct) pred
  newWanteds <- for (zip wanteds' wanteds) \case
    (Nothing, _) -> return Nothing
    (Just pred, ct) -> do
      ev <- GHC.Tc.Plugin.newWanted (ctLoc ct) pred
      return $ Just (mkNonCanonical ev)

  let substEvidence ct ct' = evCast (ctEvExpr $ ctEvidence ct') $ pluginCo (ctPred ct') (ctPred ct)
  let removedGivens = [(substEvidence ct ct', ct) | (Just ct', ct) <- zip newGivens givens]
  -- let removedDeriveds = [(evByFiat "myplugin" (ctPred ct') (ctPred ct), ct) | (Just ct', ct) <- zip newDeriveds deriveds]
  let removedWanteds = [(substEvidence ct ct', ct) | (Just ct', ct) <- zip newWanteds wanteds]

  tcPluginTrace "---Plugin solve---" $ ppr givens $$ ppr wanteds
  tcPluginTrace "---Plugin newGivens---" $ ppr newGivens
  -- tcPluginTrace "---Plugin newDeriveds---" $ ppr $ catMaybes newDeriveds
  tcPluginTrace "---Plugin newWanteds---" $ ppr $ catMaybes newWanteds
  tcPluginTrace "---Plugin removedGivens---" $ ppr removedGivens
  -- tcPluginTrace "---Plugin removedDeriveds---" $ ppr removedDeriveds
  tcPluginTrace "---Plugin removedWanteds---" $ ppr removedWanteds
  -- return $
  --   TcPluginOk
  --     (removedGivens ++ removedDeriveds ++ removedWanteds)
  --     (catMaybes $ newGivens ++ newDeriveds ++ newWanteds)
  return $
    TcPluginOk
      (removedGivens ++ removedWanteds)
      (catMaybes $ newGivens ++ newWanteds)

mtraverseType :: Applicative m => (Type -> m (Maybe Type)) -> Type -> m (Maybe Type)
mtraverseType fn = \case
  t | Just t' <- tcView t -> mtraverseType fn t'
  tv@(TyVarTy v) -> pure Nothing
  (AppTy t1 t2) ->
    ( \r1 r2 ->
        if isNothing r1 && isNothing r2
          then Nothing
          else Just $ AppTy (fromMaybe t1 r1) (fromMaybe t2 r2)
    )
      <$> fn t1 <*> fn t2
  (TyConApp tc args) ->
    traverse fn args <&> \args' ->
      if all isNothing args'
        then Nothing
        else Just $ TyConApp tc $ zipWith fromMaybe args args'
  t@(ForAllTy _tv _ty) -> pure Nothing
  (FunTy k1 k2 t1 t2) ->
    ( \r1 r2 ->
        if isNothing r1 && isNothing r2
          then Nothing
          else Just $ FunTy k1 k2 (fromMaybe t1 r1) (fromMaybe t2 r2)
    )
      <$> fn t1 <*> fn t2
  l@(LitTy _) -> pure Nothing
  (CastTy ty co) -> fn ty <&> \case Nothing -> Nothing; Just t -> Just $ CastTy t co
  co@(CoercionTy _) -> pure Nothing

data TypeDictCon = Cons | End | Lift deriving (Show)
instance Outputable TypeDictCon where
  ppr End = "End"
  ppr Cons = "Cons"
  ppr Lift = "Lift"

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
import Control.Monad (guard, (>=>))
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
  , dScopeFam :: TyCon
  , dKArg :: TyCon
  , dDictDefFam :: TyCon
  , cache :: IORef (UniqFM TyCon (UniqFM FastString (Type, Type), Type, UniqSet FastString))
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
  cache <- tcPluginIO $ newIORef emptyUFM

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

  let substitute :: Maybe TyCon -> Type -> TcPluginM (Maybe Type)
      substitute defsTyCon t =
        tryFollow (return Nothing) t splitTyConApp_maybe \case
          (tycon, args)
            | tycon == dToConstraintCachedFam -> do
                let [constr] = args
                tryFollow'' constr Nothing $ splitTyConApp_maybe >=> \case
                  (constrTyCon, []) -> Just do
                    cache' <- tcPluginIO $ readIORef cache
                    let newDict = (emptyUFM, fromJust $ lookupUFM dictDefs constrTyCon, emptyUniqSet)
                    let dict = lookupWithDefaultUFM cache' newDict constrTyCon
                    constr@(constrDict, constrRest, _) <- extractDict dict
                    let cache'' = addToUFM cache' constrTyCon constr
                    tcPluginIO $ writeIORef cache cache''
                    case splitTyConApp_maybe constrRest of
                      Just (tycon, []) | tycon == endTyCon -> do
                        let constrs = nonDetEltsUFM constrDict
                        constrs' <- for constrs \(kind, elem) ->
                          if kind `eqType` constraintKind
                            then maybe elem id <$> substitute defsTyCon elem
                            else error $ "expected a constraint, found " ++ showPprUnsafe (ppr kind $$ ppr elem)
                        case constrs' of
                          [c] -> return $ Just c
                          _ -> do
                            let arity = length constrs
                            return $ Just $ mkTyConApp (cTupleTyCon arity) constrs'
                      _ -> return Nothing
                  _ -> Nothing
            | tycon == dScopeFam -> do
                let [k, scope, block] = args
                tryFollow'' scope Nothing $ splitTyConApp_maybe >=> \case
                  (defsTyCon', []) -> Just $ substitute (Just defsTyCon') block
                  _ -> Nothing
            | tycon == dKArg -> do
                case defsTyCon of
                  Nothing -> return Nothing
                  Just defsTyCon' -> do
                    let [k, key] = args
                    tryFollow' key Nothing isStrLitTy \key' -> do
                      cache' <- tcPluginIO $ readIORef cache
                      let newDict = (emptyUFM, fromJust $ lookupUFM dictDefs defsTyCon', emptyUniqSet)
                      let dict = lookupWithDefaultUFM cache' newDict defsTyCon'
                      defs@(defsDict, defsRest, _) <- extractDict dict  -- TODO laziness: extractDictUntil
                      let cache'' = addToUFM cache' defsTyCon' defs
                      tcPluginIO $ writeIORef cache cache''
                      case lookupUFM defsDict key' of
                        Nothing -> 
                          case splitTyConApp_maybe defsRest of
                            Just (tycon, []) | tycon == endTyCon ->
                              error $ "key not present in defs " ++ showPprUnsafe (ppr key' $$ ppr defsDict)
                            _ -> return Nothing
                        Just (kind, val) -> substitute defsTyCon val <&> (<|> Just val)
            | otherwise -> mtraverseType (substitute defsTyCon) t
          where
            extractDict ::
              (UniqFM FastString (Type, Type), Type, UniqSet FastString)
              -> TcPluginM (UniqFM FastString (Type, Type), Type, UniqSet FastString)
            extractDict old@(dict, rest, removed) =
              tryFollow'' rest old $ splitTyConApp_maybe >=> \case
                (tycon, dargs)
                  | tycon == consTyCon -> Just $
                      let [_, named, dRest] = dargs
                      in tryFollow (return old) named splitTyConApp_maybe \case
                            (_, [kind, name, value]) ->
                              tryFollow' name old isStrLitTy \case
                                name'
                                  | name' `elementOfUniqSet` removed ->
                                      extractDict (dict, dRest, removed)
                                  | otherwise ->
                                      tryFollow' name old isStrLitTy \name' ->
                                        extractDict (addToUFM dict name' (kind, value), dRest, removed)
                  | tycon == dRemoveFam -> Just $ do
                      let [name, rest'] = dargs
                      tryFollow' name old isStrLitTy \name' ->
                        extractDict (dict, rest', removed `addOneToUniqSet` name')
                  | tycon == endTyCon -> Just $ return old
                  | otherwise -> Nothing

            subAndRe :: (Type -> TcPluginM b) -> b -> Type -> TcPluginM b
            subAndRe fn old x =
              substitute defsTyCon x >>= \case
                Nothing -> return old
                Just rest' -> fn rest'

            tryFollow' :: Type -> b -> (Type -> Maybe a) -> (a -> TcPluginM b) -> TcPluginM b
            tryFollow' x b deCon fn =
              tryFollow (subAndRe (\x' -> tryFollow' x' b deCon fn) b x) x deCon fn

            tryFollow'' :: Type -> b -> (Type -> Maybe (TcPluginM b)) -> TcPluginM b
            tryFollow'' x b fn = tryFollow' x b fn id

  let substituteCt (ctPred -> pred) = substitute Nothing pred

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

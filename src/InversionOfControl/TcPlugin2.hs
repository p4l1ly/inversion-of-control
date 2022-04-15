{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ViewPatterns #-}

module InversionOfControl.TcPlugin2 where

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
import GHC.Data.FastString (fsLit)
import GHC.Driver.Plugins (Plugin (..), defaultPlugin, purePlugin)
import GHC.Plugins
import GHC.Stack
import GHC.Tc.Plugin
import GHC.Tc.Types
import GHC.Tc.Types.Constraint
import GHC.Tc.Types.Evidence
import GHC.TcPluginM.Extra
import qualified GHC.TcPluginM.Extra as TcPluginM
import GHC.Types.Name.Occurrence (mkDataOcc, mkTcOcc)
import GHC.Types.Unique.FM
import GHC.Unit.Module (mkModuleName)
import GHC.Utils.Outputable (Outputable (..), text, ($$), (<+>))

plugin :: Plugin
plugin =
  defaultPlugin
    { tcPlugin = \args -> do
        opts <- foldr id defaultOpts <$> traverse parseArgument args
        return $
          tracePlugin
            "inversion-of-control"
            TcPlugin
              { tcPluginInit = lookupExtraDefs
              , tcPluginSolve = solve opts
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
  , dNotFoundTyCon :: TyCon
  , dToConstraintFam :: TyCon
  , typedictTyCon :: TyCon
  }

lookupExtraDefs :: TcPluginM ExtraDefs
lookupExtraDefs = do
  tcPluginTrace "---Plugin init---" (ppr ())
  liftModule <- lookupModule (mkModuleName "InversionOfControl.Lift") (fsLit "inversion-of-control")
  typeDictModule <- lookupModule (mkModuleName "InversionOfControl.TypeDict") (fsLit "inversion-of-control")

  getkFam <- tcLookupTyCon =<< lookupName typeDictModule (mkTcOcc "GetK")
  getFam <- tcLookupTyCon =<< lookupName typeDictModule (mkTcOcc "Get")
  incFam <- tcLookupTyCon =<< lookupName liftModule (mkTcOcc "Inc")
  kTyCon <- tcLookupTyCon =<< lookupName liftModule (mkTcOcc "K")
  kDataCon <- tcLookupDataCon =<< lookupName liftModule (mkDataOcc "K")
  peanTyCon <- tcLookupTyCon =<< lookupName liftModule (mkTcOcc "Pean")
  zeroDataCon <- tcLookupDataCon =<< lookupName liftModule (mkDataOcc "Zero")
  dConsDataCon <- tcLookupDataCon =<< lookupName typeDictModule (mkDataOcc ":+:")
  dEndDataCon <- tcLookupDataCon =<< lookupName typeDictModule (mkDataOcc "End")
  dLiftFam <- tcLookupTyCon =<< lookupName typeDictModule (mkTcOcc "LiftTags")
  dNotFoundTyCon <- tcLookupTyCon =<< lookupName typeDictModule (mkTcOcc "NotFound")
  dToConstraintFam <- tcLookupTyCon =<< lookupName typeDictModule (mkTcOcc "ToConstraint")
  typedictTyCon <- tcLookupTyCon =<< lookupName typeDictModule (mkTcOcc "TypeDict")
  return ExtraDefs{..}

solve :: Opts -> ExtraDefs -> [Ct] -> [Ct] -> [Ct] -> TcPluginM TcPluginResult
solve Opts{..} ExtraDefs{..} givens deriveds wanteds = do
  let endTyCon = promoteDataCon dEndDataCon
  let consTyCon = promoteDataCon dConsDataCon
  let kPromTyCon = promoteDataCon kDataCon
  let zeroTyCon = promoteDataCon zeroDataCon
  let isK t = case tyConAppTyCon_maybe t of
        Nothing -> False
        Just tHead -> eqType (mkTyConTy tHead) (mkTyConTy (promoteDataCon kDataCon))
  let subst = map fst $ mkSubst' $ givens ++ deriveds
  let substUFM = listToUFM $ map fst $ catMaybes $ GHC.TcPluginM.Extra.mkSubst <$> givens ++ deriveds
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
      reduce eqK t = case splitTyConApp_maybe t of
        Nothing -> return Nothing
        Just (tycon, args)
          | tycon == getkFam -> do
              let [sym, d] = args
              tryFollow (return Nothing) sym isStrLitTy \key -> do
                let lookupTypeDict top dRec = tryFollow' dRec splitTyConApp_maybe \case
                      (tycon, dargs)
                        | tycon == endTyCon ->
                            Just $ mkTyConApp kPromTyCon [mkTyConApp zeroTyCon [], mkTyConApp dNotFoundTyCon [sym]]
                        | tycon == dLiftFam ->
                            let [dRest] = dargs
                             in Just $ mkTyConApp incFam [fromJust $ lookupTypeDict False dRest]
                        | tycon == consTyCon ->
                            let [kind, named, dRest] = dargs
                             in tryFollow' kind tyConAppTyCon_maybe \case
                                  kindTyCon
                                    | kindTyCon == kTyCon ->
                                        tryFollow' named splitTyConApp_maybe getIfKeyEqual
                                          <|> lookupTypeDict False dRest
                                    | otherwise -> lookupTypeDict False dRest
                        | otherwise -> error "GetK: expected End, LiftTags, or (:+:)"
                      where
                        tryFollow' = tryFollow $ guard (not top) >> Just (mkTyConApp getkFam [sym, dRec])
                        getIfKeyEqual (_, [_, sym', value]) =
                          tryFollow' sym' isStrLitTy \key' -> guard (key == key') >> Just value
                case lookupTypeDict True d of
                  Nothing -> return Nothing
                  Just dsub -> do
                    dsub' <- reduce False dsub
                    tcPluginTrace "---Plugin dsub---" $ ppr sym $$ ppr d $$ ppr dsub $$ ppr dsub'
                    -- TODO unless eqK, replace with K n t and create eqK
                    return $ dsub' <|> Just dsub
          | tycon == dToConstraintFam -> do
              tcPluginTrace "---Plugin toConstraint---" $ ppr t
              let descend :: [Type] -> Type -> TcPluginM (Maybe [Type])
                  descend result dRec = tryFollow' dRec splitTyConApp_maybe \case
                    (tycon, dargs)
                      | tycon == endTyCon -> return $ Just result
                      | tycon == consTyCon ->
                          let [_, named, dRest] = dargs
                           in tryFollow' named splitTyConApp_maybe \case
                                (_, [kind, name, value])
                                  | tcIsConstraintKind kind ->
                                      reduce False value >>= \case
                                        Nothing -> descend (value : result) dRest
                                        Just value' -> descend (value' : result) dRest
                                  | otherwise ->
                                      tryFollow' kind tyConAppTyCon_maybe \case
                                        kindTyCon
                                          | kindTyCon == typedictTyCon ->
                                              descend result value >>= \case
                                                Nothing -> descend (mkTyConApp dToConstraintFam [value] : result) dRest
                                                Just result' -> descend result' dRest
                                          | otherwise -> do
                                              tcPluginTrace "---Plugin toConstraint Err1---" $ ppr kindTyCon $$ ppr kind $$ ppr name $$ ppr value
                                              error "ToConstraint: expected Constraint or TypeDict kind"
                      | otherwise -> do
                          tcPluginTrace "---Plugin toConstraint Err2---" $ ppr tycon $$ ppr dargs
                          error "ToConstraint: expected End or (:+:)"
                    where
                      tryFollow' = tryFollow case result of
                        [] -> return Nothing
                        _ -> return $ Just $ mkTyConApp dToConstraintFam [dRec] : result

              descend [] (head args) >>= \case
                Just constrs -> do
                  tcPluginTrace "---Plugin toConstraint constrs---" $ ppr args $$ ppr constrs
                  case constrs of
                    [c] -> return $ Just c
                    _ -> do
                      let arity = length constrs
                      cTupleTyCon <- tcLookupTyCon (cTupleTyConName arity)
                      return $ Just $ mkTyConApp cTupleTyCon constrs
                Nothing -> return Nothing
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
  tcPluginTrace "---Plugin deriveds---" $ ppr ()
  deriveds' <- mapM reduceCt deriveds
  tcPluginTrace "---Plugin wanteds---" $ ppr ()
  wanteds' <- mapM reduceCt wanteds

  let pluginCo = mkUnivCo (PluginProv "myplugin") Representational
  newGivens <- for (zip givens' givens) \case
    (Nothing, _) -> return Nothing
    (Just pred, ct) ->
      let ev = evCast (ctEvExpr $ ctEvidence ct) $ pluginCo (ctPred ct) pred
       in Just . mkNonCanonical <$> GHC.TcPluginM.Extra.newGiven (ctLoc ct) pred ev
  newDeriveds <- for (zip deriveds' deriveds) \case
    (Nothing, _) -> return Nothing
    (Just pred, ct) -> Just . mkNonCanonical <$> GHC.TcPluginM.Extra.newDerived (ctLoc ct) pred
  newWanteds <- for (zip wanteds' wanteds) \case
    (Nothing, _) -> return Nothing
    (Just pred, ct) -> do
      ev <- GHC.TcPluginM.Extra.newWanted (ctLoc ct) pred
      return $ Just (mkNonCanonical ev)

  let substEvidence ct ct' = evCast (ctEvExpr $ ctEvidence ct') $ pluginCo (ctPred ct') (ctPred ct)
  let removedGivens = [(substEvidence ct ct', ct) | (Just ct', ct) <- zip newGivens givens]
  let removedDeriveds = [(evByFiat "myplugin" (ctPred ct') (ctPred ct), ct) | (Just ct', ct) <- zip newDeriveds deriveds]
  let removedWanteds = [(substEvidence ct ct', ct) | (Just ct', ct) <- zip newWanteds wanteds]

  tcPluginTrace "---Plugin solve---" $ ppr givens $$ ppr deriveds $$ ppr wanteds
  tcPluginTrace "---Plugin newGivens---" $ ppr newGivens
  tcPluginTrace "---Plugin newDeriveds---" $ ppr $ catMaybes newDeriveds
  tcPluginTrace "---Plugin newWanteds---" $ ppr $ catMaybes newWanteds
  tcPluginTrace "---Plugin removedGivens---" $ ppr removedGivens
  tcPluginTrace "---Plugin removedDeriveds---" $ ppr removedDeriveds
  tcPluginTrace "---Plugin removedWanteds---" $ ppr removedWanteds
  return $
    TcPluginOk
      (removedGivens ++ removedDeriveds ++ removedWanteds)
      (catMaybes $ newGivens ++ newDeriveds ++ newWanteds)

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

{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE ViewPatterns #-}

module InversionOfControl.TcPlugin where

import Data.Maybe (isNothing)
import Control.Arrow ((>>>))
import Control.Monad (unless)
import Data.Functor ((<&>))
import Data.Kind
import Data.Traversable (for)
import GHC.Builtin.Types
import GHC.Plugins
import GHC.TcPlugin.API
import GHC.TcPlugin.API.Internal
import qualified Data.Set as S

plugin :: GHC.Plugins.Plugin
plugin =
  GHC.Plugins.defaultPlugin
    { GHC.Plugins.tcPlugin =
        Just . GHC.TcPlugin.API.mkTcPlugin . myTcPlugin
    , GHC.Plugins.pluginRecompile = GHC.Plugins.purePlugin
    }

myTcPlugin :: [CommandLineOption] -> GHC.TcPlugin.API.TcPlugin
myTcPlugin args =
  TcPlugin
    { tcPluginInit = myTcPluginInit
    , tcPluginSolve = myTcPluginSolve ("no_getK_singletonDataCon" `elem` args)
    , tcPluginRewrite = myTcPluginRewrite
    , tcPluginStop = myTcPluginStop
    }

data Env = Env
  { getkFam :: TyCon
  , kDataCon :: DataCon
  , peanTyCon :: TyCon
  }

myTcPluginStop :: Env -> TcPluginM 'Stop ()
myTcPluginStop _ = return ()

findModule :: String -> String -> TcPluginM Init Module
findModule package name =
  findImportedModule
    (mkModuleName name)
    (Just $ fsLit package)
    <&> \case
      Found _ m -> m
      _ -> error $ "InversionOfControl.TcPlugin couldn't find " ++ name

myTcPluginInit :: TcPluginM Init Env
myTcPluginInit = do
  tcPluginTrace "---Plugin init---" (ppr ())
  liftModule <- findModule "inversion-of-control" "InversionOfControl.Lift"
  typeDictModule <- findModule "inversion-of-control" "InversionOfControl.TypeDict"
  Env
    <$> (tcLookupTyCon =<< lookupOrig typeDictModule (mkTcOcc "GetK"))
    <*> (tcLookupDataCon =<< lookupOrig liftModule (mkDataOcc "K"))
    <*> (tcLookupTyCon =<< lookupOrig liftModule (mkTcOcc "Pean"))

myTcPluginSolve :: Bool -> Env -> TcPluginSolver
myTcPluginSolve no_getK_singletonDataCon Env{getkFam, kDataCon, peanTyCon} givens wanteds = do
  tcPluginTrace "---Plugin start---" (ppr givens $$ ppr wanteds)
  if null wanteds && not no_getK_singletonDataCon
    then do
      let aliases = do
            ct <- givens
            case classifyPredType $ ctPred ct of
              EqPred NomEq a b ->
                case tyConAppTyCon_maybe a of
                  Nothing ->
                    case tyConAppTyCon_maybe b of
                      Nothing -> []
                      Just tycon
                        | eqType (mkTyConTy tycon) (mkTyConTy getkFam) -> [(ct, a)]
                        | otherwise -> []
                  Just tycon
                    | eqType (mkTyConTy tycon) (mkTyConTy getkFam) -> [(ct, b)]
                    | otherwise -> []
              _ -> []
      let isK t = case tyConAppTyCon_maybe t of
            Nothing -> False
            Just tHead -> eqType (mkTyConTy tHead) (mkTyConTy (promoteDataCon kDataCon))
      let kAliases = do
            (ctPred >>> classifyPredType -> EqPred NomEq a b) <- givens
            if isK a
              then [b]
              else if isK b then [a] else []
      let kVarAliases = S.fromList do
            alias <- kAliases
            case getTyVar_maybe alias of
              Just var -> [var]
              Nothing -> []
      tcPluginTrace "---Plugin kVarAliases---" (ppr kVarAliases)
      let kOtherAliases = filter (isNothing . getTyVar_maybe) kAliases
      let reductionExists alias = case getTyVar_maybe alias of
            Just var -> var `S.member` kVarAliases
            Nothing -> not $ null $ filter (eqType alias) kOtherAliases
      let unreducedAliases = filter (not . reductionExists . snd) aliases
      givens' <- for unreducedAliases \(ct, alias) -> do
        varN <- newFlexiTyVar (mkTyConTy peanTyCon)
        varX <- newFlexiTyVar GHC.Builtin.Types.liftedTypeKind
        let k = mkTyConApp (promoteDataCon kDataCon) [mkTyVarTy varN, mkTyVarTy varX]
        let coercion = mkPluginUnivCo "getk_returns_k" Nominal alias k
        let EvExpr evidence = evCoercion coercion
        newGiven (bumpCtLocDepth $ ctLoc ct) (mkPrimEqPredRole Nominal alias k) evidence
      unless (null givens') do
        tcPluginTrace "---Plugin apply---" (ppr givens')
      pure $ TcPluginOk [] (map mkNonCanonical givens')
    else pure $ TcPluginOk [] []

myTcPluginRewrite :: Env -> GHC.TcPlugin.API.UniqFM TyCon TcPluginRewriter
myTcPluginRewrite _ = emptyUFM

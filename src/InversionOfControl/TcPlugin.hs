{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE ViewPatterns #-}

module InversionOfControl.TcPlugin where

import Control.Arrow ((>>>))
import Control.Monad (unless)
import Data.Functor ((<&>))
import Data.Kind
import Data.Traversable (for)
import GHC.Builtin.Types
import GHC.Plugins
import GHC.TcPlugin.API
import GHC.TcPlugin.API.Internal

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
    , tcPluginSolve = myTcPluginSolve
    , tcPluginRewrite = myTcPluginRewrite
    , tcPluginStop = myTcPluginStop
    }

data Env = Env
  { unwrapFam :: TyCon
  , incFam :: TyCon
  , getkFam :: TyCon
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
    <$> (tcLookupTyCon =<< lookupOrig liftModule (mkTcOcc "Unwrap"))
    <*> (tcLookupTyCon =<< lookupOrig liftModule (mkTcOcc "Inc"))
    <*> (tcLookupTyCon =<< lookupOrig typeDictModule (mkTcOcc "GetK"))
    <*> (tcLookupDataCon =<< lookupOrig liftModule (mkDataOcc "K"))
    <*> (tcLookupTyCon =<< lookupOrig liftModule (mkTcOcc "Pean"))

myTcPluginSolve :: Env -> TcPluginSolver
myTcPluginSolve Env{getkFam, kDataCon, peanTyCon} givens wanteds = do
  tcPluginTrace "---Plugin start---" (ppr givens $$ ppr wanteds)
  if null wanteds
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
      let reductionExists alias = or do
            (ctPred >>> classifyPredType -> EqPred NomEq a b) <- givens
            return $ (eqType alias a && isK b) || (eqType alias b && isK a)
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
myTcPluginRewrite Env{unwrapFam, incFam} = emptyUFM

-- listToUFM
--   [
--     ( unwrapFam
--     , \_ [unwrapArg] ->
--         case splitTyConApp_maybe unwrapArg of
--           Nothing -> return TcPluginNoRewrite
--           Just (tycon, incArgs) ->
--             if eqType (mkTyConTy tycon) (mkTyConTy incFam)
--               then
--                 return $
--                   TcPluginRewriteTo
--                     ( Reduction
--                         ( mkPluginUnivCo
--                             "unwrap.inc=unwrap"
--                             Nominal
--                             (mkTyConApp unwrapFam [unwrapArg])
--                             (mkTyConApp unwrapFam incArgs)
--                         )
--                         (mkTyConApp unwrapFam incArgs)
--                     )
--                     []
--               else return TcPluginNoRewrite
--     )
--     -- ,
--     --   ( getkFam
--     --   , \givens [sym, dict] -> do
--     --       let isK t = case tyConAppTyCon_maybe t of
--     --             Nothing -> False
--     --             Just tHead -> eqType (mkTyConTy tHead) (mkTyConTy (promoteDataCon kDataCon))
--     --           isThis t = case splitTyConApp_maybe t of
--     --             Nothing -> False
--     --             Just (tHead, tArgs) ->
--     --               eqType (mkTyConTy tHead) (mkTyConTy getkFam)
--     --                 && let [sym0, dict0] = tArgs in eqType sym0 sym && eqType dict0 dict
--     --           reductionExists = or do
--     --             (ctPred >>> classifyPredType -> EqPred NomEq a b) <- givens
--     --             return $ (isThis a && isK b) || (isThis b && isK a)
--     --       if reductionExists
--     --         then return TcPluginNoRewrite
--     --         else do
--     --           tcPluginTrace "---Plugin GetK---" (ppr givens $$ ppr sym $$ ppr dict)
--     --           varN <- newFlexiTyVar (mkTyConTy peanTyCon)
--     --           varX <- newFlexiTyVar GHC.Builtin.Types.anyTy
--     --           let k = mkTyConApp (promoteDataCon kDataCon) [mkTyVarTy varN, mkTyVarTy varX]
--     --           let getk = mkTyConApp getkFam [sym, dict]
--     --           -- (rewriteEnvCtLoc -> loc) <- askRewriteEnv
--     --           -- given' <- newWanted loc (mkPrimEqPredRole Nominal getk k)
--     --           return $
--     --             TcPluginRewriteTo
--     --               (Reduction (mkPluginUnivCo "getk_returns_k" Nominal getk k) k)
--     --               []
--     --   )
--   ]

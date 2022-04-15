{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ViewPatterns #-}

module InversionOfControl.TcPlugin where

import Control.Arrow ((>>>))
import Control.Monad (unless)
import Data.Functor ((<&>))
import Data.Kind
import qualified Data.Map as M
import Data.Maybe (isNothing, maybeToList)
import qualified Data.Set as S
import Data.Traversable (for)
import GHC.Builtin.Types
import GHC.Generics (Generic)
import GHC.Plugins
import GHC.TcPlugin.API
import qualified GHC.TcPluginM.Extra as E

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
  , getFam :: TyCon
  , incFam :: TyCon
  , kTyCon :: TyCon
  , kDataCon :: DataCon
  , peanTyCon :: TyCon
  , zeroDataCon :: DataCon
  , dConsDataCon :: DataCon
  , dEndDataCon :: DataCon
  , dLiftDataCon :: DataCon
  , dNotFoundTyCon :: TyCon
  , dNameDataCon :: DataCon
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

  getkFam <- tcLookupTyCon =<< lookupOrig typeDictModule (mkTcOcc "GetK")
  getFam <- tcLookupTyCon =<< lookupOrig typeDictModule (mkTcOcc "Get")
  incFam <- tcLookupTyCon =<< lookupOrig liftModule (mkTcOcc "Inc")
  kTyCon <- tcLookupTyCon =<< lookupOrig liftModule (mkTcOcc "K")
  kDataCon <- tcLookupDataCon =<< lookupOrig liftModule (mkDataOcc "K")
  peanTyCon <- tcLookupTyCon =<< lookupOrig liftModule (mkTcOcc "Pean")
  zeroDataCon <- tcLookupDataCon =<< lookupOrig liftModule (mkDataOcc "Zero")
  dConsDataCon <- tcLookupDataCon =<< lookupOrig typeDictModule (mkDataOcc ":+:")
  dEndDataCon <- tcLookupDataCon =<< lookupOrig typeDictModule (mkDataOcc "End")
  dLiftDataCon <- tcLookupDataCon =<< lookupOrig typeDictModule (mkDataOcc "LiftTags")
  dNotFoundTyCon <- tcLookupTyCon =<< lookupOrig typeDictModule (mkTcOcc "NotFound")
  dNameDataCon <- tcLookupDataCon =<< lookupOrig typeDictModule (mkDataOcc "Name")
  return Env{..}

myTcPluginSolve :: Bool -> Env -> TcPluginSolver
myTcPluginSolve no_getK_singletonDataCon Env{getkFam, kDataCon, peanTyCon} givens wanteds = do
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
              else [a | isK b]
      let kVarAliases = S.fromList do
            alias <- kAliases
            case getTyVar_maybe alias of
              Just var -> [var]
              Nothing -> []
      let kOtherAliases = filter (isNothing . getTyVar_maybe) kAliases
      let reductionExists alias = case getTyVar_maybe alias of
            Just var -> var `S.member` kVarAliases
            Nothing -> any (eqType alias) kOtherAliases
      let unreducedAliases = filter (not . reductionExists . snd) aliases
      givens' <- for unreducedAliases \(ct, alias) -> do
        varN <- newFlexiTyVar (mkTyConTy peanTyCon)
        varX <- newFlexiTyVar GHC.Builtin.Types.liftedTypeKind
        let k = mkTyConApp (promoteDataCon kDataCon) [mkTyVarTy varN, mkTyVarTy varX]
        let coercion = mkPluginUnivCo "getk_returns_k" Nominal alias k
        let EvExpr evidence = evCoercion coercion
        newGiven (bumpCtLocDepth $ ctLoc ct) (mkPrimEqPredRole Nominal alias k) evidence
      if null givens'
        then do
          tcPluginTrace "---Plugin tryapply---" (ppr givens)
        else do
          tcPluginTrace "---Plugin apply---" (ppr givens')
      pure $ TcPluginOk [] (map mkNonCanonical givens')
    else pure $ TcPluginOk [] []

data TypeDictCon = Cons | End | Lift deriving (Show)
instance Outputable TypeDictCon where
  ppr End = "End"
  ppr Cons = "Cons"
  ppr Lift = "Lift"

myTcPluginRewrite :: Env -> GHC.TcPlugin.API.UniqFM TyCon TcPluginRewriter
myTcPluginRewrite
  Env
    { getkFam
    , incFam
    , dConsDataCon
    , dEndDataCon
    , dLiftDataCon
    , dNotFoundTyCon
    , dNameDataCon
    , kTyCon
    , kDataCon
    , zeroDataCon
    } =
    listToUFM
      [
        ( getkFam
        , \givens args@[sym, d] -> do
            case isStrLitTy sym of
              Nothing -> return TcPluginNoRewrite
              Just symStr -> do
                let endTyCon = promoteDataCon dEndDataCon
                let liftTyCon = promoteDataCon dLiftDataCon
                let consTyCon = promoteDataCon dConsDataCon
                let nameTyCon = promoteDataCon dNameDataCon
                let endTy = mkTyConTy endTyCon
                let liftTy = mkTyConTy liftTyCon
                let consTy = mkTyConTy consTyCon
                let dictCon (mkTyConTy -> tyconTy)
                      | eqType tyconTy endTy = Just End
                      | eqType tyconTy liftTy = Just Lift
                      | eqType tyconTy consTy = Just Cons
                      | otherwise = Nothing
                let dictOrVar x =
                      case splitTyConApp_maybe x of
                        Nothing ->
                          case getTyVar_maybe x of
                            Just v -> Just $ Left v
                            Nothing -> Nothing
                        Just (con, dargs) -> dictCon con <&> Right . (,dargs)
                let aliases = M.fromList do
                      ct <- givens
                      case classifyPredType $ ctPred ct of
                        EqPred NomEq a b -> do
                          a' <- maybeToList $ dictOrVar a
                          b' <- maybeToList $ dictOrVar b
                          case (a', b') of
                            (Left v, Left v') -> [(v, Left v'), (v', Left v)]
                            (Left v, Right d) -> [(v, Right d)]
                            (Right d, Left v) -> [(v, Right d)]
                            _ -> []
                        _ -> []
                let dictFromAlias alias = do
                      alias `M.lookup` aliases >>= \case
                        Left v -> dictFromAlias v
                        Right d -> Just d
                let getDict d =
                      case splitTyConApp_maybe d of
                        Nothing -> getTyVar_maybe d >>= dictFromAlias
                        Just (con, dargs) -> dictCon con <&> (,dargs)
                let me0 = mkTyConApp getkFam . (sym :) . (: [])
                let recur me n d =
                      case getDict d of
                        Nothing -> do
                          tcPluginTrace "---Plugin2 rewriteAdvance---" (ppr ())
                          return advanceRewrite
                        Just (con, dargs) -> case con of
                          End -> do
                            tcPluginTrace "---Plugin2 rewriteEnd---" (ppr ())
                            let notFound =
                                  mkTyConApp -- K Zero (NotFound sym)
                                    (promoteDataCon kDataCon)
                                    [ mkTyConTy $ promoteDataCon zeroDataCon
                                    , mkTyConApp dNotFoundTyCon [sym]
                                    ]
                            return $
                              TcPluginRewriteTo
                                (Reduction (mkPluginUnivCo "notFound" Nominal (me $ mkTyConApp endTyCon []) notFound) notFound)
                                []
                          Lift -> do
                            tcPluginTrace "---Plugin2 rewriteLift---" (ppr ())
                            recur (\d -> me $ mkTyConApp liftTyCon [d]) (n + 1) (head dargs)
                          Cons -> do
                            tcPluginTrace "---Plugin2 rewriteCons---" (ppr ())
                            let [kind, named, dRest] = dargs
                            let me' d = me $ mkTyConApp consTyCon [kind, named, d]
                            if eqType kind (mkTyConTy kTyCon)
                              then case splitTyConApp_maybe named of
                                Nothing -> do
                                  tcPluginTrace "---Plugin2 rewriteAdvanceCons---" (ppr ())
                                  return advanceRewrite
                                Just (_, [_, sym', k]) ->
                                  case isStrLitTy sym' of
                                    Nothing -> do
                                      tcPluginTrace "---Plugin2 rewriteAdvanceConsSym---" (ppr ())
                                      return advanceRewrite
                                    Just symStr' -> do
                                      let me' dRest = me $ mkTyConApp consTyCon [kind, mkTyConApp nameTyCon [kind, sym', k], dRest]
                                      if symStr' == symStr
                                        then do
                                          tcPluginTrace "---Plugin2 found---" (ppr ())
                                          let k' = iterate (mkTyConApp incFam . return) k !! n -- TODO k' could have explicit n, not using Inc
                                          let coercion = mkPluginUnivCo "typedictFound" Nominal (me' dRest) k'
                                          return $ TcPluginRewriteTo (Reduction coercion k') []
                                        else do
                                          tcPluginTrace "---Plugin2 rewriteNext---" (ppr ())
                                          recur me' n dRest
                                Just err -> do
                                  tcPluginTrace "---Plugin2 error---" (ppr err)
                                  error "(Name sym x) expected"
                              else do
                                tcPluginTrace "---Plugin2 rewriteNextByKind---" (ppr ())
                                recur me' n dRest
                      where
                        advance = mkTyConApp getkFam [sym, d]
                        advanceRewrite =
                          TcPluginRewriteTo
                            (Reduction (mkPluginUnivCo "typedictAdvance" Nominal (me d) advance) advance)
                            []

                tcPluginTrace "---Plugin2 start---" (ppr sym $$ ppr d $$ ppr givens $$ ppr () $$ ppr (E.flattenGivens givens))
                case getDict d of
                  Nothing -> do
                    tcPluginTrace "---Plugin2 norewrite---" (ppr aliases)
                    return TcPluginNoRewrite
                  Just (con, dargs) -> do
                    tcPluginTrace "---Plugin2 rewrite---" (ppr aliases)
                    recur me0 0 d
        )
      ]

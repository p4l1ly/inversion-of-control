{-# LANGUAGE UnicodeSyntax #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# OPTIONS_GHC -fplugin InversionOfControl.TcPlugin #-}

module InversionOfControl.Recursion.IORefGraph where

import Data.Functor.Compose
import qualified Data.Array as A
import qualified Data.HashMap.Strict as HM
import Data.Semigroup
import Data.Fix
import InversionOfControl.Recursion
import InversionOfControl.Lift
import System.Mem.StableName
import Data.IORef
import Data.Hashable
import InversionOfControl.LiftN
import InversionOfControl.TypeDict
import Control.Monad
import Control.Monad.Reader
import Control.Monad.Free
import InversionOfControl.KFn
import GHC.TypeLits (Symbol)
import Data.Kind

data Ref x = Ref (StableName (IORef (Word, x))) (IORef (Word, x))

instance Show (Ref x) where
  show (Ref name _) = '@' : show (hashStableName name)

instance Eq (Ref x) where
  Ref sn1 _ == Ref sn2 _ = sn1 == sn2

instance Hashable (Ref x) where
  hashWithSalt salt (Ref sn _) = hashWithSalt salt sn

buildTopo :: Word -> x -> IO (Ref x)
buildTopo topo x = do
  ioref <- newIORef (topo, x)
  name <- makeStableName ioref
  return $ Ref name ioref

newtype RefFix f = RefFix (Ref (f (RefFix f)))
  deriving newtype Show

-- Copy-pasted from Relude
foldMapM :: forall b m f a . (Monoid b, Monad m, Foldable f) => (a -> m b) -> f a -> m b
foldMapM f xs = foldr step return xs mempty
  where
    step x r z = f x >>= \y -> r $! z `mappend` y

buildFoldable :: Foldable f => f (RefFix f) -> IO (RefFix f)
buildFoldable fr = do
  Max topo <- (`foldMapM` fr) \(RefFix (Ref _ r)) -> Max . fst <$> readIORef r
  RefFix <$> buildTopo topo fr

buildFree :: Traversable f => Free f (RefFix f) -> IO (RefFix f)
buildFree free = do
  free' <- forM free \r@(RefFix (Ref _ ior)) -> do
    (topo, _) <- readIORef ior
    return $ (topo, r)
  (snd <$>) $ (`iterM` free') \fr -> do
    fr' <- sequence fr
    let Max topo = foldMap (Max . fst) fr'
    let topo' = topo + 1
    r <- RefFix <$> buildTopo topo' (fmap snd fr')
    return (topo', r)


type RecT p a bx = ReaderT (IORef (HM.HashMap (p, StableName (IORef (Word, a))) bx))

runRecT :: forall n0 p a bx m0 x.
  (Monad m0, LiftN n0 IO m0) => RecT p a bx m0 x -> m0 x
runRecT act = do
  cacheRef <- liftn @n0 $ newIORef HM.empty
  runReaderT act cacheRef

data Rec n0 (m0 :: Type -> Type)
instance
  ( Monad mb
  , Monad m0
  , LiftN nb (RecT p a xb m0) mb
  , LiftN n0 IO m0
  , Eq p, Hashable p
  ) => KFn (RecurE nb (Rec n0 m0) p (Ref a) a (mb xb))
 where
  kfn algebra p r@(Ref name ioref) = do
    cacheRef <- liftn @nb @(RecT p a xb m0) ask
    cache <- liftIO' $ readIORef cacheRef
    case HM.lookup (p, name) cache of
      Just b -> return b
      Nothing -> do
        (_, f) <- liftIO' $ readIORef ioref
        result <- algebra p r f
        liftIO' $ modifyIORef' cacheRef (HM.insert (p, name) result)
        return result
   where
    liftIO' :: IO x -> mb x
    liftIO' = liftn @nb @(RecT p a xb m0) . lift . liftn @n0

data RecFix n0 (m0 :: Type -> Type)
instance
  KFn (RecurE nb (Rec n0 m0) p (Ref (f (RefFix f))) (f (RefFix f)) (mb xb))
  => KFn (RecurE nb (RecFix n0 m0) p (RefFix f) (f (RefFix f)) (mb xb))
  where
  kfn algebra p (RefFix r) =
    kfn @(RecurE nb (Rec n0 m0) p (Ref (f (RefFix f))) (f (RefFix f)) (mb xb))
      (\p r fr -> algebra p (RefFix r) fr)
      p r

-- type SemigroupM d = ReaderT ([f|p|] -> [f|r|] -> SemigroupA d [f|bx|]) [fk|m|]
-- newtype SemigroupA d b = SemigroupA {unSemigroupA :: Compose (SemigroupM d) (SemigroupM d) b}
-- 
-- deriving instance Functor [fk|m|] => Functor (SemigroupA d)
-- deriving instance Applicative [fk|m|] => Applicative (SemigroupA d)
-- 
-- data SemigroupRec
-- instance
--   ( Monad [fk|m|]
--   , Semigroup [f|p|]
--   , LiftN n IO [fk|m|]
--   , [f|r|] ~ Ref [f|a|]
--   , [f|c|] ~ Kindy (SemigroupA d)
--   , [f|b|] ~ SemigroupA d [f|bx|]
--   ) ⇒
--   Recur (K n SemigroupRec) d
--   where
--   recur algebra act = do
--     topos ∷ IORef (Word, A.Array Word (IORef (HM.HashMap [f|r|] [f|p|]))) <- liftn @n do
--       elems' <- replicateM 4 do newIORef HM.empty
--       newIORef (4, A.listArray (0, 3) elems')
--     algebrae
--       ∷ IORef
--           ( HM.HashMap
--             (StableName (IORef (Word, [f|a|])))
--             (Either [f|bx|] (SemigroupM d [f|bx|]))
--           )
--       <- liftn @n $ newIORef (HM.empty)
-- 
--     let recur p r@(Ref name ioref) = SemigroupA $ Compose do
--           liftn @(Succ n) do
--             (n, _) <- readIORef ioref
--             (sz, arr) <- readIORef topos
--             let sz':_ = dropWhile (<= n) $ iterate (*2) sz
--             arr' <- if sz' > sz
--               then do
--                 let elems = A.elems arr
--                 elems' <- replicateM (fromIntegral $ sz' - sz) do newIORef HM.empty
--                 let arr' = A.listArray (0, sz' - 1) $ elems ++ elems'
--                 writeIORef topos (sz', arr')
--                 return arr'
--               else
--                 return arr
--             modifyIORef' (arr' A.! n) (HM.insertWith (<>) r p)
-- 
--           return do
--             algebraeV <- liftn @(Succ n) do readIORef algebrae
--             case HM.lookup name algebraeV of
--               Just (Right algebra) -> do
--                 b <- algebra
--                 liftn @(Succ n) do writeIORef algebrae $ HM.insert name (Left b) algebraeV
--                 return b
--               Just (Left b) -> return b
--               Nothing -> error "Impossible"
-- 
--     let SemigroupA (Compose bef) = act
--     aft <- runReaderT bef recur
-- 
--     (sz, arr) <- liftn @n do readIORef topos
--     forM_ [sz - 1, sz - 2 .. 0] \i -> do
--       topo <- liftn @n do readIORef (arr A.! i)
--       forM_ (HM.toList topo) \(r@(Ref name ioref), p) -> do
--         (_, f) <- liftn @n do readIORef ioref
--         let SemigroupA (Compose bef) = algebra p r f
--         aft <- runReaderT bef recur
--         algebraeV <- liftn @n do readIORef algebrae
--         liftn @n do writeIORef algebrae (HM.insert name (Right aft) algebraeV)
-- 
--     runReaderT aft recur
-- 
-- data SemigroupRecFix
-- instance
--   ( Monad [fk|m|]
--   , [f|r|] ~ RefFix [fk|f|]
--   , [f|a|] ~ [fk|f|] [f|r|]
--   , Recur (K n SemigroupRec) (RecFixD d)
--   ) =>
--   Recur (K n SemigroupRecFix) d
--   where
--   recur algebra act =
--     recur @(K n SemigroupRec) @(RecFixD d)
--       (\p r fr -> algebra p (RefFix r) fr)
--       act

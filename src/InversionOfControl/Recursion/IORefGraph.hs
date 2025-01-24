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
import InversionOfControl.GMonadTrans
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

data Rec n0
instance
  ( Monad mb
  , Monad (UnliftN (Succ nb) mb)
  , LiftN nb (RecT p a xb (UnliftN (Succ nb) mb)) mb
  , LiftN n0 IO (Unlift (UnliftN nb mb))
  , Eq p, Hashable p
  ) => KFn (RecurE nb (Rec n0) p (Ref a) a (mb xb))
 where
  kfn algebra p r@(Ref name ioref) = do
    cacheRef <- liftn @nb @(RecT p a xb (UnliftN (Succ nb) mb)) ask
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
    liftIO' = liftn @nb @(RecT p a xb (UnliftN (Succ nb) mb)) . lift . liftn @n0

data RecFix n0
instance
  KFn (RecurE nb (Rec n0) p (Ref (f (RefFix f))) (f (RefFix f)) (mb xb))
  => KFn (RecurE nb (RecFix n0) p (RefFix f) (f (RefFix f)) (mb xb))
  where
  kfn algebra p (RefFix r) =
    kfn @(RecurE nb (Rec n0) p (Ref (f (RefFix f))) (f (RefFix f)) (mb xb))
      (\p r fr -> algebra p (RefFix r) fr) p r

type SemigroupTopos p a = (Word, A.Array Word (IORef (HM.HashMap (Ref a) p)))
type SemigroupAlgebrae p a xb m = HM.HashMap
  (StableName (IORef (Word, a)))
  (Either xb (SemigroupM p a xb m xb))

data SemigroupEnv p a xb m = SemigroupEnv
  { algebrae :: IORef (SemigroupAlgebrae p a xb m)
  , topos :: IORef (SemigroupTopos p a)
  }

type SemigroupM p a xb m = ReaderT (SemigroupEnv p a xb m) m
newtype SemigroupA p a xb m b = SemigroupA
  { unSemigroupA :: Compose (SemigroupM p a xb m) (SemigroupM p a xb m) b }

deriving instance Functor m => Functor (SemigroupA p a xb m)
deriving instance Applicative m => Applicative (SemigroupA p a xb m)

runSemigroupA :: forall n p a xb m b.
  (Monad m, LiftN n IO m)
  => SemigroupA p a xb m b
  -> (p -> Ref a -> a -> SemigroupA p a xb m xb)
  -> m b
runSemigroupA (SemigroupA (Compose bef)) algebra = do
  topos ∷ IORef (SemigroupTopos p a) <- liftn @n do
    elems' <- replicateM 4 do newIORef HM.empty
    newIORef (4, A.listArray (0, 3) elems')
  algebrae ∷ IORef (SemigroupAlgebrae p a xb m) <- liftn @n $ newIORef (HM.empty)

  aft :: SemigroupM p a xb m b <- runReaderT bef SemigroupEnv{algebrae, topos}

  (sz, arr) <- liftn @n do readIORef topos
  forM_ [sz - 1, sz - 2 .. 0] \i -> do
    topo <- liftn @n do readIORef (arr A.! i)
    forM_ (HM.toList topo) \(r@(Ref name ioref), p) -> do
      (_, f) <- liftn @n do readIORef ioref
      let SemigroupA (Compose bef) = algebra p r f
      aft <- runReaderT bef SemigroupEnv{algebrae, topos}
      algebraeV <- liftn @n do readIORef algebrae
      liftn @n do writeIORef algebrae (HM.insert name (Right aft) algebraeV)

  runReaderT aft SemigroupEnv{algebrae, topos}

semigroupRec :: forall n p a xb m.
  ( Monad m
  , Semigroup p
  , LiftN n IO m
  ) ⇒ p -> Ref a -> SemigroupA p a xb m xb
semigroupRec p r@(Ref name ioref) = SemigroupA $ Compose do
  SemigroupEnv{algebrae, topos} <- ask
  liftn @(Succ n) do
    (n, _) <- readIORef ioref
    (sz, arr) <- readIORef topos
    let sz':_ = dropWhile (<= n) $ iterate (*2) sz
    arr' <- if sz' > sz
      then do
        let elems = A.elems arr
        elems' <- replicateM (fromIntegral $ sz' - sz) do newIORef HM.empty
        let arr' = A.listArray (0, sz' - 1) $ elems ++ elems'
        writeIORef topos (sz', arr')
        return arr'
      else
        return arr
    modifyIORef' (arr' A.! n) (HM.insertWith (<>) r p)

  return do
    algebraeV <- liftn @(Succ n) do readIORef algebrae
    case HM.lookup name algebraeV of
      Just (Right algebra) -> do
        b <- algebra
        liftn @(Succ n) do writeIORef algebrae $ HM.insert name (Left b) algebraeV
        return b
      Just (Left b) -> return b
      Nothing -> error "Impossible"

runSemigroupAFix :: forall n p f xb m b.
  (Monad m, LiftN n IO m)
  => SemigroupA p (f (RefFix f)) xb m b
  -> (p -> RefFix f -> f (RefFix f) -> SemigroupA p (f (RefFix f)) xb m xb)
  -> m b
runSemigroupAFix act algebra =
  runSemigroupA @n act \p r fr -> algebra p (RefFix r) fr

semigroupRecFix :: forall n p f xb m.
  ( Monad m
  , Semigroup p
  , LiftN n IO m
  ) => p -> RefFix f -> SemigroupA p (f (RefFix f)) xb m xb
semigroupRecFix p (RefFix r) = semigroupRec @n p r

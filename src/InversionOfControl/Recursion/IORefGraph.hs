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
{-# LANGUAGE ConstraintKinds #-}
{-# OPTIONS_GHC -fplugin InversionOfControl.TcPlugin #-}

module InversionOfControl.Recursion.IORefGraph where

import Data.Functor.Compose
import qualified Data.Array as A
import qualified Data.HashMap.Strict as HM
import Data.Semigroup
import Data.Fix
import qualified InversionOfControl.Recursion as R
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

newtype RecT p a mb xb m0 x = RecT
  { unRecT :: ReaderT
      ( p -> Ref a -> a -> mb xb
      , IORef (HM.HashMap (p, StableName (IORef (Word, a))) xb)
      )
      m0 x
  }
  deriving newtype (Functor, Applicative, Monad)
type instance Unlift (RecT p a mb xb m0) = m0
instance MonadTrans (RecT p a mb xb) where
  lift = RecT . lift

type RunRecursionC m0 n0 = (Monad m0, LiftN n0 IO m0)

runRecursion :: forall n0 p a mb xb m0 x.
  RunRecursionC m0 n0 => RecT p a mb xb m0 x -> (p -> Ref a -> a -> mb xb) -> m0 x
runRecursion act algebra = do
  cacheRef <- liftn @n0 do newIORef HM.empty
  runReaderT (unRecT act) (algebra, cacheRef)

runRecursion_Fix :: forall n0 p f mb xb m0 x.
  RunRecursionC m0 n0
  => RecT p (f (RefFix f)) mb xb m0 x
  -> (p -> RefFix f -> f (RefFix f) -> mb xb)
  -> m0 x
runRecursion_Fix act algebra =
  runRecursion @n0 act \p r fr -> algebra p (RefFix r) fr

type M0 nb mb = UnliftN (Succ nb) mb
type RecurC n0 nb mb xb p a =
  ( Monad mb
  , Monad (UnliftN (Succ nb) mb)
  , LiftN nb (RecT p a mb xb (UnliftN (Succ nb) mb)) mb
  , LiftN n0 IO (UnliftN (Succ nb) mb)
  , Eq p, Hashable p
  ) :: Constraint

recur :: forall n0 nb mb xb p a.
  RecurC n0 nb mb xb p a => p -> Ref a -> mb xb
recur p r@(Ref name ioref) = do
  (algebra, cacheRef) <- liftn @nb @(RecT p a mb xb (M0 nb mb)) do RecT ask
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
  liftIO' = liftn @nb @(RecT p a mb xb (M0 nb mb)) . lift . liftn @n0

recur_Fix :: forall n0 nb mb xb p f.
  RecurC n0 nb mb xb p (f (RefFix f)) => p -> RefFix f -> mb xb
recur_Fix p (RefFix r) = recur @n0 @nb p r

data RecFix n0
type instance R.Algebra (R.E (K nb (RecFix n0)) p (RefFix f) (f (RefFix f)) mb xb) m0 =
  p -> RefFix f -> f (RefFix f) -> mb xb
type instance R.MonadT (R.E (K nb (RecFix n0)) p (RefFix f) (f (RefFix f)) mb xb) m0 =
  RecT p (f (RefFix f)) mb xb m0

instance
  (r ~ RefFix f, a ~ f (RefFix f), RunRecursionC m0 n0)
  => R.Recursion (R.E (K nb (RecFix n0)) p r a mb xb) m0
 where
  runRecursion = runRecursion_Fix @n0

instance
  RecurC n0 nb mb xb p (f (RefFix f))
  => KFn (R.RecE nb (RecFix n0) p (RefFix f) mb xb)
 where
  kfn = recur_Fix @n0 @nb


type MergingTopos p a = (Word, A.Array Word (IORef (HM.HashMap (Ref a) p)))
type MergingAlgebrae p a xb m = HM.HashMap
  (StableName (IORef (Word, a)))
  (Either xb (MergingM p a xb m xb))

data MergingEnv p a xb m = MergingEnv
  { algebrae :: IORef (MergingAlgebrae p a xb m)
  , topos :: IORef (MergingTopos p a)
  }

type MergingM p a xb m = ReaderT (MergingEnv p a xb m) m
newtype MergingA p a xb m c = MergingA (Compose (MergingM p a xb m) (MergingM p a xb m) c)

deriving instance Functor m => Functor (MergingA p a xb m)
deriving instance Applicative m => Applicative (MergingA p a xb m)

runMergingRecursion :: forall n p a xb m c.
  (Monad m, LiftN n IO m)
  => MergingA p a xb m c
  -> (p -> Ref a -> a -> MergingA p a xb m xb)
  -> m c
runMergingRecursion (MergingA (Compose bef)) algebra = do
  topos ∷ IORef (MergingTopos p a) <- liftn @n do
    elems' <- replicateM 4 do newIORef HM.empty
    newIORef (4, A.listArray (0, 3) elems')
  algebrae ∷ IORef (MergingAlgebrae p a xb m) <- liftn @n $ newIORef (HM.empty)

  aft :: MergingM p a xb m c <- runReaderT bef MergingEnv{algebrae, topos}

  (sz, arr) <- liftn @n do readIORef topos
  forM_ [sz - 1, sz - 2 .. 0] \i -> do
    topo <- liftn @n do readIORef (arr A.! i)
    forM_ (HM.toList topo) \(r@(Ref name ioref), p) -> do
      (_, f) <- liftn @n do readIORef ioref
      let MergingA (Compose bef) = algebra p r f
      aft <- runReaderT bef MergingEnv{algebrae, topos}
      algebraeV <- liftn @n do readIORef algebrae
      liftn @n do writeIORef algebrae (HM.insert name (Right aft) algebraeV)

  runReaderT aft MergingEnv{algebrae, topos}

mergeAndRecur :: forall n p a xb m.
  ( Monad m
  , Semigroup p
  , LiftN n IO m
  ) ⇒ p -> Ref a -> MergingA p a xb m xb
mergeAndRecur p r@(Ref name ioref) = MergingA $ Compose do
  MergingEnv{algebrae, topos} <- ask
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

runMergingRecursion_Fix :: forall n p f xb m c.
  (Monad m, LiftN n IO m)
  => MergingA p (f (RefFix f)) xb m c
  -> (p -> RefFix f -> f (RefFix f) -> MergingA p (f (RefFix f)) xb m xb)
  -> m c
runMergingRecursion_Fix act algebra =
  runMergingRecursion @n act \p r fr -> algebra p (RefFix r) fr

mergeAndRecur_Fix :: forall n p f xb m.
  ( Monad m
  , Semigroup p
  , LiftN n IO m
  ) => p -> RefFix f -> MergingA p (f (RefFix f)) xb m xb
mergeAndRecur_Fix p (RefFix r) = mergeAndRecur @n p r

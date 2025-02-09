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

type RefName x = StableName (IORef (Word, x))
data Ref x = Ref (RefName x) (IORef (Word, x))

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
  ( ReaderT
      ( p -> Ref a -> a -> mb xb
      , IORef (HM.HashMap (p, RefName a) xb)
      )
      m0 x
  )
  deriving newtype (Functor, Applicative, Monad)
type instance Unlift (RecT p a mb xb m0) = m0
instance MonadTrans (RecT p a mb xb) where
  lift = RecT . lift

type RunRecursionC m0 n0 = (Monad m0, LiftN n0 IO m0) :: Constraint

runRecursion :: forall n0 p a mb xb m0 x.
  RunRecursionC m0 n0 => RecT p a mb xb m0 x -> (p -> Ref a -> a -> mb xb) -> m0 x
runRecursion (RecT act) algebra = do
  cacheRef <- liftn @n0 do newIORef HM.empty
  runReaderT act (algebra, cacheRef)

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
  , Monad (M0 nb mb)
  , LiftN nb (RecT p a mb xb (M0 nb mb)) mb
  , LiftN n0 IO (M0 nb mb)
  , Eq p, Hashable p
  ) :: Constraint

recur :: forall n0 nb mb xb p a.
  RecurC n0 nb mb xb p a => p -> Ref a -> mb xb
recur p r@(Ref name ioref) = do
  (algebra, cacheRef) <- liftn @nb do RecT ask
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
  liftIO' = liftn @nb . lift . liftn @n0

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
type MergingCache p' a xb = HM.HashMap (RefName a) (Either p' xb)

data MergingEnv p p' a mb xb = MergingEnv
  { cache :: IORef (MergingCache p' a xb)
  , topos :: IORef (MergingTopos p a)
  , coalgebra :: p -> Ref a -> a -> mb p'
  , algebra :: p' -> mb xb
  }

newtype MergingRecT p p' a mb xb m0 c = MergingRecT
  { unMergingRecT :: ReaderT (MergingEnv p p' a mb xb) m0 c }
  deriving newtype (Functor, Applicative, Monad)
type instance Unlift (MergingRecT p p' a mb xb m0) = m0
instance MonadTrans (MergingRecT p p' a mb xb) where
  lift = MergingRecT . lift

type RunMergingRecursionC n0 m0 = (Monad m0, LiftN n0 IO m0) :: Constraint

runMergingRecursion :: forall n0 p p' a mb xb m0 c.
  RunMergingRecursionC n0 m0
  => MergingRecT p p' a mb xb m0 c
  -> (p -> Ref a -> a -> mb p')
  -> (p' -> mb xb)
  -> m0 c
runMergingRecursion (MergingRecT act) coalgebra algebra = do
  topos ∷ IORef (MergingTopos p a) <- liftn @n0 do
    elems' <- replicateM 4 do newIORef HM.empty
    newIORef (4, A.listArray (0, 3) elems')
  cache ∷ IORef (MergingCache p' a xb) <- liftn @n0 $ newIORef (HM.empty)

  let env = MergingEnv{cache, topos, coalgebra, algebra}
  runReaderT act env

runMergingRecursion_Fix :: forall n0 p p' f mb xb m0 c.
  RunMergingRecursionC n0 m0
  => MergingRecT p p' (f (RefFix f)) mb xb m0 c
  -> (p -> RefFix f -> f (RefFix f) -> mb p')
  -> (p' -> mb xb)
  -> m0 c
runMergingRecursion_Fix act coalgebra algebra = runMergingRecursion @n0 act
  do \p r fr -> coalgebra p (RefFix r) fr
  algebra

type MergeAndRecurC n0 nb mb xb p p' a =
  ( Monad mb
  , Monad (M0 nb mb)
  , LiftN nb (MergingRecT p p' a mb xb (M0 nb mb)) mb
  , LiftN n0 IO (M0 nb mb)
  , Semigroup p
  ) :: Constraint

finishDescend :: forall n0 nb mb xb p p' a.
  MergeAndRecurC n0 nb mb xb p p' a => mb ()
finishDescend = do
  MergingEnv{cache, topos, coalgebra, algebra} <- liftn @nb do MergingRecT ask
  (sz, arr) <- liftIO' do readIORef topos
  forM_ [sz - 1, sz - 2 .. 0] \i -> do
    topo <- liftIO' do readIORef (arr A.! i)
    forM_ (HM.toList topo) \(r@(Ref name ioref), p) -> do
      (_, a) <- liftIO' do readIORef ioref
      p' <- coalgebra p r a
      liftIO' do modifyIORef' cache do HM.insert name (Left p')
 where
  liftIO' :: IO x -> mb x
  liftIO' = liftn @nb @(MergingRecT p p' a mb xb (M0 nb mb)) . lift . liftn @n0

descend :: forall n0 nb mb xb p p' a.
  MergeAndRecurC n0 nb mb xb p p' a => p -> Ref a -> mb (RefName a)
descend p r@(Ref name ioref) = do
  MergingEnv{cache, topos, coalgebra, algebra} <- liftn @nb do MergingRecT ask
  liftIO' do
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
  return name
 where
  liftIO' :: IO x -> mb x
  liftIO' = liftn @nb @(MergingRecT p p' a mb xb (M0 nb mb)) . lift . liftn @n0

descend_Fix :: forall n0 nb mb xb p p' f.
  MergeAndRecurC n0 nb mb xb p p' (f (RefFix f)) => p -> RefFix f -> mb (RefName (f (RefFix f)))
descend_Fix p (RefFix r) = descend @n0 @nb p r

ascend :: forall n0 nb mb xb p p' a.
  MergeAndRecurC n0 nb mb xb p p' a => RefName a -> mb xb
ascend name = do
  MergingEnv{cache, topos, coalgebra, algebra} <- liftn @nb do MergingRecT ask
  cacheVal <- liftIO' do readIORef cache
  case HM.lookup name cacheVal of
    Just (Left p') -> do
      xb <- algebra p'
      liftIO' do writeIORef cache $ HM.insert name (Right xb) cacheVal
      return xb
    Just (Right xb) -> return xb
    Nothing -> error "not visited in descend"
 where
  liftIO' :: IO x -> mb x
  liftIO' = liftn @nb @(MergingRecT p p' a mb xb (M0 nb mb)) . lift . liftn @n0

ascend_Fix :: forall n0 nb mb xb p p' f.
  MergeAndRecurC n0 nb mb xb p p' (f (RefFix f)) => RefName (f (RefFix f)) -> mb xb
ascend_Fix r = ascend @n0 @nb r

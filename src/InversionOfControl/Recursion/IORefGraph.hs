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
import Control.Monad
import Control.Monad.Reader
import Control.Monad.Free

data Ref x = Ref (StableName (IORef (Word, x))) (IORef (Word, x))

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
    let topo = maximum $ fmap fst fr'
    let topo' = topo + 1
    r <- RefFix <$> buildTopo topo' (fmap snd fr')
    return (topo', r)


data Rec n
instance
  ( Monad m
  , Monad m'
  , Eq p
  , Hashable p
  , LiftN n' m m'
  , LiftN n IO m
  ) ⇒
  Recur (E (K n (Rec n')) p (Ref x) x (m' b) m m)
  where
  recur algebra act = do
    cacheRef <- liftn @n $ newIORef HM.empty

    let liftIO' :: IO a -> m' a
        liftIO' = liftn @n' @m . liftn @n

    let recur p r@(Ref name ioref) = do
          cache <- liftIO' $ readIORef cacheRef
          case HM.lookup (p, name) cache of
            Just b -> return b
            Nothing -> do
              (_, f) <- liftIO' $ readIORef ioref
              result <- algebra recur p r f
              liftIO' $ modifyIORef' cacheRef (HM.insert (p, name) result)
              return result

    act recur

instance
  (Monad m, Recur (E k p (Ref (f (RefFix f))) (f (RefFix f)) b m2 m)) ⇒
  Recur (E k p (RefFix f) (f (RefFix f)) b m2 m)
  where
  recur algebra act =
    recur @(E k p (Ref (f (RefFix f))) (f (RefFix f)) b m2 m)
      (\rec p r fr -> algebra (\p (RefFix r) -> rec p r) p (RefFix r) fr)
      (\rec -> act (\p (RefFix r) -> rec p r))

data SemigroupRec
instance
  ( Monad m
  , Semigroup p
  , LiftN n IO m
  ) ⇒
  Recur (E (K n SemigroupRec) p (Ref x) x (Compose m m b) (Compose m m) m)
  where
  recur algebra act = do
    topos ∷ IORef (Word, A.Array Word (IORef (HM.HashMap (Ref x) p))) <- liftn @n do
      elems' <- replicateM 4 do newIORef HM.empty
      newIORef (4, A.listArray (0, 3) elems')
    algebrae ∷ IORef (HM.HashMap (StableName (IORef (Word, x))) (Either b (m b))) <-
      liftn @n $ newIORef (HM.empty)

    let recur p r@(Ref name ioref) = Compose do
          liftn @n do
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
            algebraeV <- liftn @n do readIORef algebrae
            case HM.lookup name algebraeV of
              Just (Right algebra) -> do
                b <- algebra
                liftn @n do writeIORef algebrae $ HM.insert name (Left b) algebraeV
                return b
              Just (Left b) -> return b
              Nothing -> error "Impossible"

    let Compose bef = act recur
    aft <- bef

    (sz, arr) <- liftn @n do readIORef topos
    forM_ [sz - 1, sz - 2 .. 0] \i -> do
      topo <- liftn @n do readIORef (arr A.! i)
      forM_ (HM.toList topo) \(r@(Ref name ioref), p) -> do
        (_, f) <- liftn @n do readIORef ioref
        let Compose bef = algebra recur p r f
        aft <- bef
        algebraeV <- liftn @n do readIORef algebrae
        liftn @n do writeIORef algebrae (HM.insert name (Right aft) algebraeV)

    aft

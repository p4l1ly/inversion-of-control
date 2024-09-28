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
import InversionOfControl.MonadFn
import GHC.TypeLits (Symbol)
import Data.Kind

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
  ( Monad [fk|m|]
  , Monad [fk|bm|]
  , Eq [f|p|]
  , Hashable [f|p|]
  , LiftN (Succ n') [fk|m|] [fk|bm|]
  , LiftN n IO [fk|m|]
  , [f|r|] ~ Ref [f|a|]
  , [f|c|] ~ Kindy (ReaderT ([f|p|] -> [f|r|] -> [f|b|]) [fk|m|])
  , [f|b|] ~ [fk|bm|] [f|bx|]
  ) ⇒
  Recur (K n (Rec n')) d
  where
  recur algebra act = do
    cacheRef <- liftn @n $ newIORef HM.empty

    let liftIO' :: IO a -> [fk|bm|] a
        liftIO' = liftn @(Succ n') @[fk|m|] . liftn @n

    let recur p r@(Ref name ioref) = do
          cache <- liftIO' $ readIORef cacheRef
          case HM.lookup (p, name) cache of
            Just b -> return b
            Nothing -> do
              (_, f) <- liftIO' $ readIORef ioref
              result <- algebra p r f
              liftIO' $ modifyIORef' cacheRef (HM.insert (p, name) result)
              return result

    runReaderT act recur

data RecFix n
instance
  ( Monad [fk|m|]
  , [f|r|] ~ RefFix [fk|f|]
  , [f|a|] ~ [fk|f|] [f|r|]
  , Recur (K n (Rec n')) (RecFixD d)
  ) =>
  Recur (K n (RecFix n')) d
  where
  recur algebra act =
    recur @(K n (Rec n')) @(RecFixD d)
      (\p r fr -> algebra p (RefFix r) fr)
      act

data RecFixD d
type instance Definition (RecFixD d) =
  Name "a" ([fk|f|] (RefFix [fk|f|]))
  :+: Name "r" (Ref [fs|a|])
  :+: Follow d

data FixAskRun (f :: Type -> Type) (m :: Type -> Type)
data FixRecurD (name :: Symbol) d drest
type instance Definition (FixRecurD name d drest) =
  Name name (FixAskRun [fk|f|] [fk|m|])
  :+: Follow (LiftUp drest)

instance
  ( LiftN n (ReaderT (p -> Ref (f (RefFix f)) -> bm bx) m) bm
  , Monad bm
  , Monad m
  ) => MonadFnN (E (K n (FixAskRun f m)) (p, RefFix f) bx bm) where
  monadfnn (p, RefFix r) = do
    rec <- liftn @n ask
    rec p r

-- (E k p (RefFix f) (f (RefFix f)) b m2 m)
-- (E k p (Ref (f (RefFix f))) (f (RefFix f)) b m2 m)

-- data SemigroupRec
-- instance
--   ( Monad m
--   , Semigroup p
--   , LiftN n IO m
--   ) ⇒
--   Recur (E (K n SemigroupRec) p (Ref x) x (Compose m m b) (Compose m m) m)
--   where
--   recur algebra act = do
--     topos ∷ IORef (Word, A.Array Word (IORef (HM.HashMap (Ref x) p))) <- liftn @n do
--       elems' <- replicateM 4 do newIORef HM.empty
--       newIORef (4, A.listArray (0, 3) elems')
--     algebrae ∷ IORef (HM.HashMap (StableName (IORef (Word, x))) (Either b (m b))) <-
--       liftn @n $ newIORef (HM.empty)
-- 
--     let recur p r@(Ref name ioref) = Compose do
--           liftn @n do
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
--             algebraeV <- liftn @n do readIORef algebrae
--             case HM.lookup name algebraeV of
--               Just (Right algebra) -> do
--                 b <- algebra
--                 liftn @n do writeIORef algebrae $ HM.insert name (Left b) algebraeV
--                 return b
--               Just (Left b) -> return b
--               Nothing -> error "Impossible"
-- 
--     let Compose bef = act recur
--     aft <- bef
-- 
--     (sz, arr) <- liftn @n do readIORef topos
--     forM_ [sz - 1, sz - 2 .. 0] \i -> do
--       topo <- liftn @n do readIORef (arr A.! i)
--       forM_ (HM.toList topo) \(r@(Ref name ioref), p) -> do
--         (_, f) <- liftn @n do readIORef ioref
--         let Compose bef = algebra recur p r f
--         aft <- bef
--         algebraeV <- liftn @n do readIORef algebrae
--         liftn @n do writeIORef algebrae (HM.insert name (Right aft) algebraeV)
-- 
--     aft

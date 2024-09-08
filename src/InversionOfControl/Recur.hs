{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}

module InversionOfControl.Recur where

import Control.Monad
import Control.Monad.Trans
import InversionOfControl.Lift
import InversionOfControl.LiftN
import Data.Kind
-- import Data.Functor.Compose

data Explicit (k :: K) (n' :: Pean) (r :: Type) (fr :: Type)
type family Ek e :: K where
  Ek (Explicit k _ _ _) = k
type family En' e :: Pean where
  En' (Explicit _ n' _ _) = n'
type family Er e :: Type where
  Er (Explicit _ _ r _) = r
type family Efr e :: Type where
  Efr (Explicit _ _ _ fr) = fr

type family Et (e :: Type) :: (Type -> Type) -> Type -> Type

class (Monad m, MonadTrans (Et e), Monad (Et e m)) => Recur e b m where
  runRecur ::
    forall m' a.
    (Monad m', LiftN (En' e) (Et e m) m') =>
    ((Er e -> m' b) -> Efr e -> m' b) ->
    ((Er e -> m' b) -> Et e m a) ->
    m a

newtype BeforeAfter m a = BeforeAfter (m (m a))

instance Functor m => Functor (BeforeAfter m) where
  fmap f (BeforeAfter bef) = BeforeAfter (fmap (fmap f) bef)

instance Applicative m => Applicative (BeforeAfter m) where
  pure a = BeforeAfter (pure (pure a))
  BeforeAfter bef1 <*> BeforeAfter bef2 = BeforeAfter $ (<*>) <$> bef1 <*> bef2

runBeforeAfter :: Monad m => BeforeAfter m a -> m a
runBeforeAfter (BeforeAfter bef) = join bef

-- class (Monad m, Applicative (Et e m), Monoid p) => HyloRecur e b p m where
--   -- TODO support composed applicative functors where (Et e m) is (En' e) levels deep
--   runHyloRecur ::
--     ((Er e -> m ()) -> Efr e -> m ()) ->
--     ((Er e -> p -> Et e m b) -> Efr e -> p -> Et e m b) ->
--     ((Er e -> m ()) -> m ()) ->
--     ((Er e -> p -> Et e m b) -> Et e m a) ->
--     m a

-- TODO this is very specific around BeforeAfter
class (Monad m, Monoid p) => HyloRecur e b p m where
  runHyloRecur ::
    ((Er e -> m ()) -> Efr e -> m ()) ->
    ((Er e -> p -> BeforeAfter m b) -> Efr e -> p -> BeforeAfter m b) ->
    ((Er e -> m ()) -> m ()) ->
    ((Er e -> p -> BeforeAfter m b) -> BeforeAfter m a) ->
    m a

{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module InversionOfControl.MonadFn where

import Control.Monad.Trans (MonadTrans (lift))
import InversionOfControl.Lift (K (K), Pean (Succ, Zero), Unwrap)
import Data.Kind

type family Param (k :: Type) :: Type
type family Result (k :: Type) :: Type

data Explicit (a :: Type) (b :: Type) (k :: Type)
type instance Param (Explicit a _ _) = a
type instance Result (Explicit _ b _) = b

class Monad m => MonadFn0 (k :: Type) (m :: Type -> Type) where
  monadfn0 :: Param k -> m (Result k)

class Monad m => MonadFn (k :: K) (m :: Type -> Type) where
  monadfn :: Param (Unwrap k) -> m (Result (Unwrap k))

instance MonadFn0 k m => MonadFn ('K Zero k) m where
  monadfn :: Param k -> m (Result k)
  monadfn = monadfn0 @k

instance
  (MonadFn ('K n k) m, MonadTrans mt, Monad m, Monad (mt m)) =>
  MonadFn ('K (Succ n) k) (mt m)
  where
  monadfn ::
    (MonadFn ('K n k) m, MonadTrans mt, Monad m, Monad (mt m)) =>
    Param (Unwrap ('K ('Succ n) k)) ->
    mt m (Result (Unwrap ('K ('Succ n) k)))
  monadfn p1 = lift (monadfn @('K n k) p1)

type MonadFn' k a b m = (MonadFn k m, b ~ Result (Unwrap k), a ~ Param (Unwrap k))

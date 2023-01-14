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

type family Param (k :: *) :: *
type family Result (k :: *) :: *

data Explicit (a :: *) (b :: *) (k :: *)
type instance Param (Explicit a _ _) = a
type instance Result (Explicit _ b _) = b

class Monad m => MonadFn0 (k :: *) (m :: * -> *) where
  monadfn0 :: Param k -> m (Result k)

class Monad m => MonadFn (k :: K) (m :: * -> *) where
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

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE UndecidableInstances #-}

module InversionOfControl.Lift where

data Pean = Zero | Succ Pean

data K = K Pean *
data Unreachable

type family Unwrap (x :: K) = (r :: *) where
  Unwrap ('K _ k) = k

type family Inc (k :: K) = (r :: K) where
  Inc ('K n x) = 'K (Succ n) x

type family LiftCount (k :: K) :: Pean where
  LiftCount ('K n _) = n

type family Inherit (mk :: * -> *) (k :: K) :: K where
  Inherit mk k = 'K (LiftCount k) (mk (Unwrap k))

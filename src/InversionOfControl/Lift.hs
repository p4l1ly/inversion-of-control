{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UnicodeSyntax #-}

module InversionOfControl.Lift where

import Data.Kind

data Pean = Zero | Succ Pean

data K = K Pean Type
data Unreachable

type family Unwrap (x ∷ K) = (r ∷ Type) where
  Unwrap ('K _ k) = k

type family Inc (k ∷ K) = (r ∷ K) where
  Inc ('K n x) = 'K (Succ n) x

type family LiftCount (k ∷ K) ∷ Pean where
  LiftCount ('K n _) = n

type family Inherit (mk ∷ Type → Type) (k ∷ K) ∷ K where
  Inherit mk k = 'K (LiftCount k) (mk (Unwrap k))

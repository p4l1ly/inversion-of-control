{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UnicodeSyntax #-}

module InversionOfControl.Lift where

import Data.Kind

data Zero
data Succ n

data K pean x
data Unreachable

type family Unwrap x = (r ∷ Type) where
  Unwrap (K _ k) = k

type family Inc (k ∷ Type) = (r ∷ Type) where
  Inc (K n x) = K (Succ n) x

type family LiftCount (k ∷ Type) ∷ Type where
  LiftCount (K n _) = n

type family Inherit (mk ∷ Type → Type) (k ∷ Type) ∷ Type where
  Inherit mk k = K (LiftCount k) (mk (Unwrap k))

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE UndecidableInstances #-}

module InversionOfControl.Lift where

data Pean = Zero | Succ Pean

data K = K Pean *
data Unreachable

type Wrap (k :: *) = 'K Zero k

type family Unwrap (x :: K) = (r :: *) where
  Unwrap ( 'K _ k) = k

-- Note:  In ghc-8.10.7,
-- haskell type checker cannot infer that
-- forall k. x is invariant in "Inc k"
type family Inc (k :: K) = (r :: K) where
  Inc ( 'K n x) = 'K (Succ n) x

type family LiftCount (k :: K) :: Pean where
  LiftCount ( 'K n _) = n

type family Mk (mk :: * -> *) (k :: K) :: K where
  Mk mk k = 'K (LiftCount k) (mk (Unwrap k))

type family MkN (mk :: Pean -> * -> *) (k :: K) :: K where
  MkN mk k = 'K Zero (mk (LiftCount k) (Unwrap k))

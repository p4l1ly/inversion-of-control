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
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UnicodeSyntax #-}
{-# LANGUAGE QuasiQuotes #-}

module InversionOfControl.KFn where

import Data.Kind
import GHC.TypeLits (Symbol)
import InversionOfControl.Lift (K, Succ, Zero)
import InversionOfControl.GMonadTrans

data E (k :: Type) (kfn :: Type)
type family EKfn (e :: Type) where
  EKfn (E _ kfn) = kfn

class KFn e where
  kfn :: EKfn e

class KFnAuto e where
  kfnAuto ∷ EKfn e

type KE n k kfn = E (K n k) kfn
type KE0 k kfn = KE Zero k kfn

instance
  ( KFnAuto (KE n k (x -> Unlift m y))
  , GMonadTrans m
  , Monad m
  , Monad (Unlift m)
  )
  ⇒ KFnAuto (KE (Succ n) k (x -> m y))
  where
  kfnAuto x = glift (kfnAuto @(E (K n k) _) x)

data Lifter
instance KFnAuto (KE0 Lifter (x -> x)) where
  kfnAuto x = x

instance KFnAuto (KE n Lifter kfn) => KFn (KE n Lifter kfn) where
  kfn = kfnAuto @(E (K n Lifter) kfn)

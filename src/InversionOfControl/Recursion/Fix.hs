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
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# OPTIONS_GHC -fplugin InversionOfControl.TcPlugin #-}
{-# OPTIONS_GHC -ddump-tc-trace -ddump-to-file #-}

module InversionOfControl.Recursion.Fix where

import Control.Monad.Reader
import Data.Fix
import InversionOfControl.TypeDict
import InversionOfControl.KFn
import InversionOfControl.Lift
import InversionOfControl.LiftN
import InversionOfControl.GMonadTrans
import qualified InversionOfControl.Recursion as R
import Data.Kind

newtype RecT p r mb xb m0 x =
  RecT (ReaderT (p -> r -> mb xb) m0 x)
  deriving newtype (Functor, Applicative, Monad)
type instance Unlift (RecT p r mb xb m0) = m0
instance MonadTrans (RecT p r mb xb) where
  lift = RecT . lift

runRecursion
  :: RecT p r mb xb m0 c
  -> (p -> r -> mb xb)
  -> m0 c
runRecursion (RecT act) algebra = runReaderT act algebra

type RecurC nb mb xb p r =
  ( Monad mb
  , Monad (UnliftN (Succ nb) mb)
  , LiftN nb (RecT p r mb xb (UnliftN (Succ nb) mb)) mb
  ) :: Constraint

recur :: forall nb mb xb p r.
  RecurC nb mb xb p r => p -> r -> mb xb
recur p r = do
  algebra <- liftn @nb do RecT ask
  algebra p r

data Rec
type instance R.MonadT (R.E (K nb Rec) p (Fix f) (f (Fix f)) mb xb) m0 = RecT p (Fix f) mb xb m0

instance (r ~ Fix f, a ~ f (Fix f)) => R.Recursion (R.E (K nb Rec) p r a mb xb) m0 where
  runRecursion act algebra = runRecursion act (\p r@(Fix a) -> algebra p r a)

instance RecurC nb mb xb p r => KFn (R.RecE nb Rec p r mb xb) where
  kfn = recur @nb

runMergingRecursion_Fix ::
  Monad mb
  => RecT p (Fix f) mb xb m0 c
  -> (p -> Fix f -> f (Fix f) -> mb p')
  -> (p' -> mb xb)
  -> m0 c
runMergingRecursion_Fix act coalgebra algebra = runRecursion act
  (\p r@(Fix fr) -> coalgebra p r fr >>= algebra)

descend_Fix :: forall nb mb xb p r.
  RecurC nb mb xb p r => p -> r -> mb xb
descend_Fix = recur @nb

finishDescend :: Applicative mb => mb ()
finishDescend = pure ()

ascend_Fix :: Applicative mb => xb -> mb xb
ascend_Fix = pure

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

newtype RecT p f mb xb m0 x =
  RecT { unRecT :: ReaderT (p -> Fix f -> f (Fix f) -> mb xb) m0 x }
  deriving newtype (Functor, Applicative, Monad)

type instance Unlift (RecT p f mb xb m0) = m0
instance MonadTrans (RecT p f mb xb) where
  lift = RecT . lift

runRecursion
  :: RecT p f mb xb m0 c
  -> (p -> Fix f -> f (Fix f) -> mb xb)
  -> m0 c
runRecursion act algebra = runReaderT (unRecT act) algebra

type RecurC nb mb xb p f =
  ( Monad mb
  , Monad (UnliftN (Succ nb) mb)
  , LiftN nb (RecT p f mb xb (UnliftN (Succ nb) mb)) mb
  ) :: Constraint

recur :: forall nb mb xb p f a.
  RecurC nb mb xb p f => p -> Fix f -> mb xb
recur p r@(Fix fr) = do
  algebra <- liftn @nb do RecT ask
  algebra p r fr

data Rec
type instance R.Algebra (K _ Rec) p (Fix f) (f (Fix f)) b =
  p -> Fix f -> f (Fix f) -> b
type instance R.MonadT (K _ Rec) p (Fix f) (f (Fix f)) (mb xb) m0 c = RecT p f mb xb m0 c

instance R.Recursion (K nb Rec) p (Fix f) (f (Fix f)) (mb xb) m0 c where
  runRecursion = runRecursion

instance RecurC nb mb xb p f => KFn (R.RecE nb Rec p (Fix f) (mb xb)) where
  kfn = recur @nb

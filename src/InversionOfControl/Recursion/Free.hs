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

module InversionOfControl.Recursion.Free where

import Control.Monad.Reader
import Control.Monad.Free
import qualified InversionOfControl.Recursion as R
import InversionOfControl.Lift
import InversionOfControl.LiftN
import InversionOfControl.GMonadTrans
import InversionOfControl.TypeDict
import InversionOfControl.KFn
import Data.Kind

newtype RecT p f a mb xb m0 x =
  RecT { unRecT :: ReaderT (p -> Free f a -> f (Free f a) -> mb xb, p -> a -> mb xb) m0 x }
  deriving newtype (Functor, Applicative, Monad)
type instance Unlift (RecT p f a mb xb m0) = m0
instance MonadTrans (RecT p f a mb xb) where
  lift = RecT . lift

runRecursion
  :: RecT p f a mb xb m0 c
  -> (p -> a -> mb xb)
  -> (p -> Free f a -> f (Free f a) -> mb xb)
  -> m0 c
runRecursion act goLeaf algebra = runReaderT (unRecT act) (algebra, goLeaf)

type RecurC nb mb xb p f a =
  ( Monad mb
  , Monad (UnliftN (Succ nb) mb)
  , LiftN nb (RecT p f a mb xb (UnliftN (Succ nb) mb)) mb
  ) :: Constraint

recur :: forall nb mb m0 xb p f a.
  RecurC nb mb xb p f a => p -> Free f a -> mb xb
recur p r = do
  (algebra, goLeaf) <- liftn @nb do RecT ask
  case r of
    Free fr -> algebra p r fr
    Pure a -> goLeaf p a

data RecPure
type instance R.MonadT (R.E (K nb RecPure) p (Free f xb) (f (Free f xb)) mb xb) m0 = RecT p f xb mb xb m0

instance
  (r ~ Free f xb, a ~ f (Free f xb), Applicative mb)
  => R.Recursion (R.E (K nb RecPure) p r a mb xb) m0
 where
  runRecursion act = runRecursion act (\_ -> pure)

instance RecurC nb mb xb p f xb => KFn (R.RecE nb RecPure p (Free f xb) mb xb) where
  kfn = recur @nb

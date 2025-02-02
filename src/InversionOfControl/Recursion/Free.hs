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
{-# OPTIONS_GHC -fplugin InversionOfControl.TcPlugin #-}

module InversionOfControl.Recursion.Free where

import Control.Monad.Reader
import Control.Monad.Free
import InversionOfControl.Recursion
import InversionOfControl.Lift
import InversionOfControl.LiftN
import InversionOfControl.TypeDict
import InversionOfControl.KFn
import Data.Kind

type RecT p f a b = ReaderT
  ( p -> Free f a -> f (Free f a) -> b
  , p -> a -> b
  )

runRecursion
  :: RecT p f a b m0 c
  -> (p -> a -> b)
  -> (p -> Free f a -> f (Free f a) -> b)
  -> m0 c
runRecursion act goLeaf algebra = runReaderT act (algebra, goLeaf)

type RecurC n0 nb mb xb p f a =
  ( Monad mb
  , Monad (UnliftN (Succ nb) mb)
  , LiftN nb (RecT p f a (mb xb) (UnliftN (Succ nb) mb)) mb
  ) :: Constraint

recur :: forall n0 nb mb xb p f a.
  RecurC n0 nb mb xb p f a => p -> Free f a -> mb xb
recur p r = do
  (algebra, goLeaf) <- liftn @nb ask
  case r of
    Free fr -> algebra p r fr
    Pure a -> goLeaf p a

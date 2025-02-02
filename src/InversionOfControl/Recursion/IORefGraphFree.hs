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
{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE ConstraintKinds #-}
{-# OPTIONS_GHC -fplugin InversionOfControl.TcPlugin #-}

module InversionOfControl.Recursion.IORefGraphFree where

import Control.Monad.Free
import InversionOfControl.TypeDict
import InversionOfControl.Recursion
import InversionOfControl.Lift
import InversionOfControl.LiftN
import qualified InversionOfControl.Recursion.Free as F
import qualified InversionOfControl.Recursion.IORefGraph as G
import InversionOfControl.GMonadTrans
import Control.Monad.Reader
import Data.Hashable
import Data.Kind

newtype Ref f = Ref (Free f (G.Ref (Ref f)))

type RecT p f b = ReaderT (p -> Ref f -> f (Ref f) -> b)

type M0 nb mb = Unlift (Unlift (UnliftN nb mb))
type M1 nb mb xb p f = RecT p f (mb xb) (M0 nb mb)
type M2 nb mb xb p f = G.RecT p (Ref f) mb xb (M1 nb mb xb p f)

type RunRecursionC n0 nb mb xb p f c =
  ( G.RunRecursionC (M1 nb mb xb p f) (Succ n0)
  , G.RecurC (Succ n0) nb mb xb p (Ref f)
  , Functor f
  ) :: Constraint

runRecursion :: forall n0 nb mb xb p f c.
  RunRecursionC n0 nb mb xb p f c
  => M2 nb mb xb p f c
  -> (p -> Ref f -> f (Ref f) -> mb xb)
  -> M0 nb mb c
runRecursion act algebra = do
  runReaderT
    do G.runRecursion @(Succ n0) act \p gr r@(Ref free) -> do
        case free of
          Free ffree -> algebra p (Ref (Pure gr)) (fmap Ref ffree)
          Pure gr' -> G.recur @(Succ n0) @nb p gr'
    algebra

type RecurC n0 nb mb xb p f =
  ( Monad mb
  , Monad (M0 nb mb)
  , LiftN (Succ nb) (M1 nb mb xb p f) mb
  , G.RecurC (Succ n0) nb mb xb p (Ref f)
  , Functor f
  ) :: Constraint

recur :: forall n0 nb mb xb p f.
  RecurC n0 nb mb xb p f => p -> Ref f -> mb xb
recur p r@(Ref free) = case free of
  Pure gr' -> G.recur @(Succ n0) @nb p gr'
  Free ffree -> do
    algebra <- liftn @(Succ nb) ask
    algebra p (Ref free) (fmap Ref ffree)

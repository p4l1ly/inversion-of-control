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
{-# OPTIONS_GHC -fplugin InversionOfControl.TcPlugin #-}

module InversionOfControl.Recursion.IORefGraphFree0 where

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

newtype Ref f = Ref (Free f (G.Ref (Ref f)))

type M0 nb mb = Unlift (Unlift (UnliftN nb mb))
type M1 nb mb xb p f = F.RecT p f (G.Ref (Ref f)) (mb xb) (M0 nb mb)
type M2 nb mb xb p f = G.RecT p (Ref f) mb xb (M1 nb mb xb p f)

runRecursion :: forall n0 nb mb xb p f c.
  ( G.RunRecursionC (M1 nb mb xb p f) (Succ n0)
  , F.RecurC n0 (Succ nb) mb xb p f (G.Ref (Ref f))
  , G.RecurC (Succ n0) nb mb xb p (Ref f)
  , Functor f
  )
  => M2 nb mb xb p f c
  -> (p -> Ref f -> f (Ref f) -> (mb xb))
  -> M0 nb mb c
runRecursion act algebra = do
  F.runRecursion
    do G.runRecursion @(Succ n0) act \p gr r@(Ref free) -> F.recur @n0 @(Succ nb) p free
    do \p gr -> G.recur @(Succ n0) @nb p gr
    do \p free ffree -> algebra p (Ref free) (fmap Ref ffree)

recur :: forall n0 nb mb xb p f.
  F.RecurC n0 (Succ nb) mb xb p f (G.Ref (Ref f)) => p -> Ref f -> mb xb
recur p r@(Ref free) = F.recur @n0 @(Succ nb) p free

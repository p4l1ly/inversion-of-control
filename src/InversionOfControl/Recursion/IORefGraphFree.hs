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

newtype Ref f = Ref (Free f (G.Ref (Ref f)))

type M0 nb mb = Unlift (Unlift (UnliftN nb mb))
type M1 nb mb xb p f = F.RecT p f (G.Ref (Ref f)) (mb xb) (M0 nb mb)
type M2 nb mb xb p f = G.RecT p (Ref f) mb xb (M1 nb mb xb p f)

runRecursion :: forall n0 nb mb xb p f c.
  ( G.RunRecursionC (M1 nb mb xb p f) (Succ n0)
  , G.RecurC (Succ n0) nb mb xb p (Ref f)
  , Functor f
  )
  => M2 nb mb xb p f c
  -> (p -> Ref f -> f (Ref f) -> (mb xb))
  -> M0 nb mb c
runRecursion act algebra = do
  F.runRecursion
    do G.runRecursion @(Succ n0) act \p gr r@(Ref free) -> do
        -- For total code reuse, it could be implemented this way:
        -- `F.recur @n0 @(Succ nb) p free`
        -- But we want to support one specialty for better sharing - run algebra with
        -- `Pure gr` instead of `Free free` passed as the reference parameter.
        case free of
          Free ffree -> algebra p (Ref (Pure gr)) (fmap Ref ffree)
          Pure gr' -> G.recur @(Succ n0) @nb p gr'
    do \p gr -> G.recur @(Succ n0) @nb p gr
    do \p free ffree -> algebra p (Ref free) (fmap Ref ffree)

recur :: forall n0 nb mb xb p f a.
  ( G.RecurC (Succ n0) nb mb xb p (Ref f)
  , F.RecurC n0 (Succ nb) mb xb p f (G.Ref (Ref f))
  ) => p -> Ref f -> mb xb
recur p r@(Ref free) = case free of
  Pure gr' -> G.recur @(Succ n0) @nb p gr'
  -- We do the Pure/Free match twice. If we'd want to avoid this, we should additionally store the
  -- base algebra itself. There's actually not much to reuse in Free recursion then, so we can
  -- actually stop using it.
  _ -> F.recur @n0 @(Succ nb) p free

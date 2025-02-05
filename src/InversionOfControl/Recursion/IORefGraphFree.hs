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
import qualified InversionOfControl.Recursion as R
import InversionOfControl.KFn
import InversionOfControl.Lift
import InversionOfControl.LiftN
import qualified InversionOfControl.Recursion.IORefGraph as G
import qualified InversionOfControl.Recursion.Free as F
import InversionOfControl.GMonadTrans
import Control.Monad.Reader
import Data.Hashable
import Data.Kind

newtype Ref f = Ref (Free f (G.Ref (Ref f))) deriving Show

type M1 mb xb p f m0 = F.RecT p f (G.Ref (Ref f)) mb xb m0
type M2 mb xb p f m0 = G.RecT p (Ref f) mb xb (M1 mb xb p f m0)

newtype RecT p f mb xb m0 x = RecT
  { unRecT :: M2 mb xb p f m0 x }
  deriving newtype (Functor, Applicative, Monad)
type instance Unlift (RecT p f mb xb m0) = M2 mb xb p f m0
instance {-# OVERLAPS #-} Monad m0 => GMonadTrans (RecT p f mb xb m0) where
  glift = RecT

type RunRecursionC n0 nb m0 mb xb p f =
  ( G.RunRecursionC (M1 mb xb p f m0) (Succ n0)
  , G.RecurC (Succ n0) (Succ nb) mb xb p (Ref f)
  , Functor f
  ) :: Constraint

runRecursion :: forall n0 nb p f mb xb m0 x.
  RunRecursionC n0 nb m0 mb xb p f
  => RecT p f mb xb m0 x
  -> (p -> Ref f -> f (Ref f) -> mb xb)
  -> m0 x
runRecursion act algebra = do
  F.runRecursion
    do G.runRecursion @(Succ n0) (unRecT act) \p gr r@(Ref free) -> do
        -- The naive implementation would be `F.recur @(Succ nb) p free` but then we would never
        -- get references to G.Ref in the algebra. We want to pass `Pure gr` instead of its content
        -- if we are directly under it.
        case free of
          Free ffree -> algebra p (Ref (Pure gr)) (fmap Ref ffree)
          Pure gr' -> G.recur @(Succ n0) @(Succ nb) p gr'
    do \p gr -> G.recur @(Succ n0) @(Succ nb) p gr
    do \p free ffree -> algebra p (Ref free) (fmap Ref ffree)

type RecurC nb mb xb p f = F.RecurC (Succ (Succ nb)) mb xb p f (G.Ref (Ref f))

recur :: forall n0 nb mb xb p f.
  RecurC nb mb xb p f => p -> Ref f -> mb xb
recur p r@(Ref free) = F.recur @(Succ (Succ nb)) p free

data (Rec n0)
type instance R.Algebra (R.E (K nb (Rec n0)) p (Ref f) (f (Ref f)) mb xb) m0 =
  p -> Ref f -> f (Ref f) -> mb xb
type instance R.MonadT (R.E (K nb (Rec n0)) p (Ref f) (f (Ref f)) mb xb) m0 =
  RecT p f mb xb m0
instance
  (r ~ Ref f, a ~ f (Ref f), RunRecursionC n0 nb m0 mb xb p f)
  => R.Recursion (R.E (K nb (Rec n0)) p r a mb xb) m0 where
  runRecursion act algebra = runRecursion @n0 @nb act algebra
instance RecurC nb mb xb p f => KFn (R.RecE nb (Rec n0) p (Ref f) mb xb) where
  kfn = recur @n0 @nb

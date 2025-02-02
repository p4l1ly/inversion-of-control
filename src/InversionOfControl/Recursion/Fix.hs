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
{-# OPTIONS_GHC -fplugin InversionOfControl.TcPlugin #-}
{-# OPTIONS_GHC -ddump-tc-trace -ddump-to-file #-}

module InversionOfControl.Recursion.Fix where

import Control.Monad.Reader
import Data.Fix
import InversionOfControl.TypeDict
import InversionOfControl.KFn
import InversionOfControl.Lift
import InversionOfControl.LiftN
import InversionOfControl.Recursion

data Rec
instance KFn (RecurE n Rec p (Fix f) (f (Fix f)) b) where
  kfn algebra p r@(Fix a) = algebra p r a

type RecT p f b = ReaderT (p -> Fix f -> f (Fix f) -> b)

runRecursion :: RecT p f b m0 c -> (p -> (Fix f) -> (f (Fix f)) -> b) -> m0 c
runRecursion act algebra = runReaderT act algebra

recur :: forall n0 nb mb xb p f.
  ( Monad mb
  , Monad (UnliftN (Succ nb) mb)
  , LiftN nb (RecT p f (mb xb) (UnliftN (Succ nb) mb)) mb
  ) => p -> Fix f -> mb xb
recur p r@(Fix fr) = do
  algebra <- liftn @nb @(RecT p f (mb xb) (UnliftN (Succ nb) mb)) ask
  algebra p r fr

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

module InversionOfControl.Recursion.Fix where

import Data.Monoid
import Data.Fix
import InversionOfControl.Recursion
import InversionOfControl.Lift
import Control.Monad.Reader
import InversionOfControl.TypeDict

data Rec
instance
  ( Traversable [fk|f|]
  , Monad [fk|m|]
  , [f|r|] ~ Fix [fk|f|]
  , [f|a|] ~ [fk|f|] [f|r|]
  , [f|c|] ~ Kindy (ReaderT ([f|p|] -> [f|r|] -> [f|b|]) [fk|m|])
  ) ⇒
  Recur (K n Rec) d
  where
  recur algebra act = do
    let rec p r@(Fix fr) = algebra p r fr
    runReaderT act rec

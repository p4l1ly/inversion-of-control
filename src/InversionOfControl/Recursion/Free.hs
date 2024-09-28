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

module InversionOfControl.Recursion.Free where

import Data.Monoid
import Control.Monad.Free
import InversionOfControl.Recursion
import InversionOfControl.Lift
import InversionOfControl.TypeDict
import Control.Monad.Reader

data Rec
instance
  ( Traversable [fk|f|]
  , Monad [fk|m|]
  , Applicative [fk|bm|]
  , [f|b|] ~ [fk|bm|] [f|bx|]
  , [f|r|] ~ Free [fk|f|] [f|bx|]
  , [f|a|] ~ [fk|f|] [f|r|]
  , [f|c|] ~ Kindy (ReaderT ([f|p|] -> [f|r|] -> [f|b|]) [fk|m|])
  ) ⇒
  Recur (K n Rec) d
  where
  recur algebra act = do
    let rec p r@(Free a) = algebra p r a
        rec p r@(Pure b) = pure b
    runReaderT act rec

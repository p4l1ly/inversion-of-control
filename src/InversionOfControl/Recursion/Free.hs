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

module InversionOfControl.Recursion.Free where

import Data.Monoid
import Control.Monad.Free
import InversionOfControl.Recursion
import InversionOfControl.Lift

data Rec
instance (Traversable f, Monad m) ⇒ Recur (E (K n Rec) p (Free f b) (f (Free f b)) b m m)
  where
  recur algebra act = do
    let rec p r@(Free a) = algebra rec p r a
        rec p r@(Pure b) = b
    act rec

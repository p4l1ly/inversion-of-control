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

import Control.Monad.Free
import InversionOfControl.Recursion
import InversionOfControl.Lift
import InversionOfControl.TypeDict
import InversionOfControl.KFn

data Rec
instance
  ( Applicative [fk|bm|]
  , [f|b|] ~ [fk|bm|] [f|bx|]
  , [f|r|] ~ Free [fk|f|] [f|bx|]
  , [f|a|] ~ [fk|f|] [f|r|]
  ) ⇒
  KFn (K n Rec) (Recur d)
  where
  kfn (algebra, p, r@(Free a)) = algebra p r a
  kfn (algebra, p, r@(Pure bx)) = pure bx

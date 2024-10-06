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

import Data.Fix
import InversionOfControl.TypeDict
import InversionOfControl.Recursion
import InversionOfControl.KFn
import InversionOfControl.Lift

data Rec
instance
  ( [f|r|] ~ Fix [fk|f|]
  , [f|a|] ~ [fk|f|] [f|r|]
  ) ⇒
  KFn (K n Rec) (Recur d)
  where
  kfn (algebra, p, r@(Fix a)) = algebra p r a

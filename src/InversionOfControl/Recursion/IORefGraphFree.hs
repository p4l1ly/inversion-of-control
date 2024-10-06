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
import InversionOfControl.Recursion.IORefGraph
import InversionOfControl.MonadFn
import InversionOfControl.GMonadTrans
import Control.Monad.Reader

type FRef f = Free f (RefFix (Free f))

data FRec n
instance
  ( Monad [fk|m|]
  , [f|r|] ~ FRef [fk|f|]
  , [f|a|] ~ [fk|f|] [f|r|]
  , Recur (K n (RecFix n')) (FRecD d)
  , [f|b|] ~ [fk|bm|] [f|bx|]
  , [f|c|] ~ Kindy (ReaderT ([f|p|] -> Ref [f|r|] -> [f|b|]) [fk|m|])
  , LiftN n' [fk|c|] [fk|bm|]
  , Monad [fk|bm|]
  ) => Recur (K n (FRec n')) d
  where
  recur algebra act =
    recur @(K n (RecFix n')) @(FRecD d)
      (\p r fr -> recFree p fr)
      act
    where
      recFree p r@(Free a) = algebra p r a
      recFree p r@(Pure rr) =
        monadfnn
          @( E
              (K n' (GetFam "fixrec" (Follow (FixRecurD "fixrec" (FRecD d) Empty))))
              ([f|p|], RefFix (Free [fk|f|]))
              [f|bx|]
              [fk|bm|]
          )
          (p, rr)

data FRecD d
type instance Definition (FRecD d) =
  Name "f" (Kindy (Free [fk|f|]))
  :+: Name "r" (RefFix [fsk|f|])
  :+: Name "a" ([fsk|f|] [fs|r|])
  :+: Follow d


-- TODO There's a better way than ReaderT. One can pass its algebra as a parameter to rec every time
-- and we will do the right mechanism. This will resolve also the problem of this instance where we
-- would have to add another two stacks of ReaderT - one for internal operation and one for the
-- user.

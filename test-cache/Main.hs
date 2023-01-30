{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -ddump-tc-trace -ddump-to-file #-}
{-# OPTIONS_GHC -fplugin InversionOfControl.TcPlugin #-}

module Main where

import Data.Kind
import GHC.TypeLits
import InversionOfControl.Lift
import InversionOfControl.TypeDict

data Dict1 (d :: * -> *) :: *
data Dict2 (d :: *) :: *
data Dict3 :: *

class Ok (x :: *)

data A :: *
data B :: *
data C :: *
data D :: *

instance Ok A
instance Ok B
instance Ok C

type instance
  Definition (Dict1 d) =
    Name "xx" (Ok (Get "x" (Follow (d (Dict1 d)))))
      :+: (Get "cont" (Follow (d Dict3)) :: TypeDict)

type instance
  Definition (Dict2 d) =
    Name "x" A
      :+: Name "cont" (Name "y" (Ok B) :+: Follow d)
      :+: End

type instance
  Definition Dict3 =
    Name "z" (Ok C)
      :+: End

main :: IO ()
main = do
  fun @Dict2
  funLift
  funDeep

fun :: forall d. ToConstraint (Follow (Dict1 d)) => IO ()
fun = return ()

data E
type instance
  Definition E =
    Name "lift" ()
      :+: Name "k" ()
      :+: Name "x" ()
      :+: Name "y" ()
      :+: Name "z" ()
      :+: End

funLift ::
  ( LiftsUntil "k" (Name "k" () :+: End) ~ Zero
  , LiftsUntil
      "k"
      ( Name "lift" ()
          :+: Name "g" Bool
          :+: Name "lift" ()
          :+: Name "k" ()
          :+: End
      )
      ~ Succ (Succ Zero)
  , LiftsUntil
      "k"
      ( Name "g" Bool
          :+: Name "lift" ()
          :+: Follow E
      )
      ~ Succ (Succ Zero)
  , LiftsUntil "y" (Follow E) ~ Succ Zero
  , LiftsUntil "z" (Follow E) ~ Succ Zero
  , LiftsUntil "x" (Follow E) ~ Succ Zero
  ) =>
  IO ()
funLift = return ()

funDeep ::
  forall d.
  ( Get "x" (Follow (LiftUp d)) ~ Get "x" (Follow d)
  , LiftsUntil "x" (Follow (LiftUp d)) ~ Succ (LiftsUntil "x" (Follow d))
  ) =>
  IO ()
funDeep = return ()

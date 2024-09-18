{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UnicodeSyntax #-}
{-# OPTIONS_GHC -ddump-tc-trace -ddump-to-file #-}
{-# OPTIONS_GHC -fplugin InversionOfControl.TcPlugin #-}

module Main where

import Data.Kind
import GHC.TypeLits
import InversionOfControl.Lift
import InversionOfControl.TypeDict

data Dict1 (d ∷ Type → Type) ∷ Type
data Dict2 (d ∷ Type) ∷ Type
data Dict3 ∷ Type

class Ok (x ∷ Type)

data A ∷ Type
data B ∷ Type
data C ∷ Type

instance Ok A
instance Ok B
instance Ok C

type instance
  Definition (Dict1 d) =
    Name "xx" (ConstraintVal (Ok (Get "x" (Follow (d (Dict1 d))))))
      :+: Get "cont" (Follow (d Dict3))

type instance
  Definition (Dict2 d) =
    Name "x" A
      :+: Name "cont" (Name "y" (ConstraintVal (Ok B)) :+: Follow d)
      :+: End

type instance
  Definition Dict3 =
    Name "z" (ConstraintVal (Ok C))
      :+: End

main ∷ IO ()
main = do
  fun @Dict2
  funLift
  funDeep

fun ∷ ∀ d. ToConstraint (Follow (Dict1 d)) ⇒ IO ()
fun = return ()

data D
type instance
  Definition D =
    Name "lift" ()
      :+: Name "k" ()
      :+: Name "x" ()
      :+: Name "y" ()
      :+: Name "z" ()
      :+: End

funLift
  ∷ ( LiftsUntil "k" (Name "k" () :+: End) ~ Zero
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
            :+: Follow D
        )
        ~ Succ (Succ Zero)
    , LiftsUntil "y" (Follow D) ~ Succ Zero
    , LiftsUntil "z" (Follow D) ~ Succ Zero
    , LiftsUntil "x" (Follow D) ~ Succ Zero
    )
  ⇒ IO ()
funLift = return ()

-- The type family `WaitPlugin` prevents the type checker to reduce `Get "x" y ~ Get "x" z` to
-- `y ~ z` before the TC plugin is run. The plugin simply removes `WaitPlugin`.
-- Sadly, `Get` should logically be a type family, not a `Type -> Type`, but it would be forbidden
-- under forall (see test-free/DictImpl.hs).
funDeep
  ∷ ∀ d
   . ( WaitPlugin (Get "x" (Follow (LiftUp d))) ~ WaitPlugin (Get "x" (Follow d))
     , LiftsUntil "x" (Follow (LiftUp d)) ~ Succ (LiftsUntil "x" (Follow d))
     )
  ⇒ IO ()
funDeep = return ()

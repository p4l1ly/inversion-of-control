{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -ddump-tc-trace -ddump-to-file #-}
{-# OPTIONS_GHC -fplugin InversionOfControl.TcPlugin #-}

module Main where

import InversionOfControl.TypeDict
import Data.Kind
import GHC.TypeLits

data Dict1 (d :: * -> *) :: *
data Dict2 (d :: *) :: *
data Dict3 :: *

class Ok (x :: *) where

data A :: *
data B :: *
data C :: *
data D :: *

instance Ok A
instance Ok B
instance Ok C

type instance Definition (Dict1 d) =
  "bad"
    :-: Name "xx" (Ok (Get "x" (Follow (d (Dict1 d)))))
    :+: (Get "cont" (Follow (d Dict3)) :: TypeDict)

type instance Definition (Dict2 d) =
  Name "x" A
    :+: Name "cont" (Name "y" (Ok B) :+: Follow d)
    :+: End

type instance Definition Dict3 =
  Name "z" (Ok C)
    :+: Name "bad" (Ok D)
    :+: End

main :: IO ()
main = fun @Dict2

fun :: forall d. ToConstraint (Follow (Dict1 d)) => IO ()
fun = return ()

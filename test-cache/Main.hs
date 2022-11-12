{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE ConstraintKinds #-}
{-# OPTIONS_GHC -ddump-tc-trace -ddump-to-file #-}
{-# OPTIONS_GHC -fplugin InversionOfControl.TcPlugin2 #-}

module Main where

import InversionOfControl.TypeDict
import Data.Kind
import GHC.TypeLits

data DictD
data DictC

type instance DictDef DictC =
  Name "other" (Num (KArg "x"))
    :+: End

type instance DictDef DictD =
  Name "x" Bool
    :+: End

main :: IO ()
main = fun @DictC

fun :: forall d. ToConstraintCached DictC DictD => IO ()
fun = return ()

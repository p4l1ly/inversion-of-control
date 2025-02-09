{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UnicodeSyntax #-}
-- {-# OPTIONS_GHC -dcore-lint #-}
-- {-# OPTIONS_GHC -ddump-tc-trace -ddump-to-file #-}
{-# OPTIONS_GHC -fplugin InversionOfControl.TcPlugin #-}

module Main where

import Data.Kind
import InversionOfControl.MonadFn
import InversionOfControl.Lift
import InversionOfControl.TypeDict

data Even
data Odd

instance Monad m ⇒ MonadFn (E (K Zero Even) Int Bool m) where
  monadfn = return . even

instance Monad m ⇒ MonadFn (E (K Zero Odd) Int Bool m) where
  monadfn = return . odd

data OptionsD

type instance
  Definition OptionsD =
    Name "k01" Even
      :+: Name "k02" Even
      :+: Name "k03" Even
      :+: Name "k04" Even
      :+: Name "k05" Even
      :+: Name "k06" Even
      :+: Name "k07" Even
      :+: Name "k08" Even
      :+: Name "k09" Even
      :+: Name "k10" Even
      :+: Name "k11" Even
      :+: Name "k12" Even
      :+: Name "k13" Even
      :+: Name "k14" Even
      :+: Name "k15" Even
      :+: Name "k16" Even
      :+: Name "k17" Even
      :+: Name "k18" Even
      :+: Name "k19" Even
      :+: Name "k20" Even
      :+: Name "k21" Even
      :+: Name "k22" Even
      :+: Name "k23" Even
      :+: Name "k24" Even
      :+: Name "k25" Even
      :+: Name "k26" Even
      :+: Name "k27" Even
      :+: Name "k28" Odd
      :+: Name "k29" Odd
      :+: Name "k30" Odd
      :+: End

main ∷ IO ()
main = hardToCompileFn @OptionsD

data HardToCompileFnA (d ∷ Type)
type instance
  Definition (HardToCompileFnA d) =
    Name "k01" (E [k|k01|] Int Bool IO)
      :+: Name "k02" (E [k|k02|] Int Bool IO)
      :+: Name "k03" (E [k|k03|] Int Bool IO)
      :+: Name "k04" (E [k|k04|] Int Bool IO)
      :+: Name "k05" (E [k|k05|] Int Bool IO)
      :+: Name "k06" (E [k|k06|] Int Bool IO)
      :+: Name "k07" (E [k|k07|] Int Bool IO)
      :+: Name "k08" (E [k|k08|] Int Bool IO)
      :+: Name "k09" (E [k|k09|] Int Bool IO)
      :+: Name "k10" (E [k|k10|] Int Bool IO)
      :+: Name "k11" (E [k|k11|] Int Bool IO)
      :+: Name "k12" (E [k|k12|] Int Bool IO)
      :+: Name "k13" (E [k|k13|] Int Bool IO)
      :+: Name "k14" (E [k|k14|] Int Bool IO)
      :+: Name "k15" (E [k|k15|] Int Bool IO)
      :+: Name "k16" (E [k|k16|] Int Bool IO)
      :+: Name "k17" (E [k|k17|] Int Bool IO)
      :+: Name "k18" (E [k|k18|] Int Bool IO)
      :+: Name "k19" (E [k|k19|] Int Bool IO)
      :+: Name "k20" (E [k|k20|] Int Bool IO)
      :+: Name "k21" (E [k|k21|] Int Bool IO)
      :+: Name "k22" (E [k|k22|] Int Bool IO)
      :+: Name "k23" (E [k|k23|] Int Bool IO)
      :+: Name "k24" (E [k|k24|] Int Bool IO)
      :+: Name "k25" (E [k|k25|] Int Bool IO)
      :+: Name "k26" (E [k|k26|] Int Bool IO)
      :+: Name "k27" (E [k|k27|] Int Bool IO)
      :+: Name "k28" (E [k|k28|] Int Bool IO)
      :+: Name "k29" (E [k|k29|] Int Bool IO)
      :+: Name "k30" (E [k|k30|] Int Bool IO)
      :+: End

type HardToCompileFnD (d1 ∷ Type) =
  ( MonadFn [g1|k01|]
  , MonadFn [g1|k02|]
  , MonadFn [g1|k03|]
  , MonadFn [g1|k04|]
  , MonadFn [g1|k05|]
  , MonadFn [g1|k06|]
  , MonadFn [g1|k07|]
  , MonadFn [g1|k08|]
  , MonadFn [g1|k09|]
  , MonadFn [g1|k10|]
  , MonadFn [g1|k11|]
  , MonadFn [g1|k12|]
  , MonadFn [g1|k13|]
  , MonadFn [g1|k14|]
  , MonadFn [g1|k15|]
  , MonadFn [g1|k16|]
  , MonadFn [g1|k17|]
  , MonadFn [g1|k18|]
  , MonadFn [g1|k19|]
  , MonadFn [g1|k20|]
  , MonadFn [g1|k21|]
  , MonadFn [g1|k22|]
  , MonadFn [g1|k23|]
  , MonadFn [g1|k24|]
  , MonadFn [g1|k25|]
  , MonadFn [g1|k26|]
  , MonadFn [g1|k27|]
  , MonadFn [g1|k28|]
  , MonadFn [g1|k29|]
  , MonadFn [g1|k30|]
  )
    ∷ Constraint

hardToCompileFn
  ∷ ∀ d d1
   . ( d1 ~ HardToCompileFnA d
     , HardToCompileFnD d1
     )
  ⇒ IO ()
hardToCompileFn = do
  False ← monadfn @[g1|k01|] 5
  False ← monadfn @[g1|k02|] 5
  False ← monadfn @[g1|k03|] 5
  False ← monadfn @[g1|k04|] 5
  False ← monadfn @[g1|k05|] 5
  False ← monadfn @[g1|k06|] 5
  False ← monadfn @[g1|k07|] 5
  False ← monadfn @[g1|k08|] 5
  False ← monadfn @[g1|k09|] 5
  False ← monadfn @[g1|k10|] 5
  False ← monadfn @[g1|k11|] 5
  False ← monadfn @[g1|k12|] 5
  False ← monadfn @[g1|k13|] 5
  False ← monadfn @[g1|k14|] 5
  False ← monadfn @[g1|k15|] 5
  False ← monadfn @[g1|k16|] 5
  False ← monadfn @[g1|k17|] 5
  False ← monadfn @[g1|k18|] 5
  False ← monadfn @[g1|k19|] 5
  False ← monadfn @[g1|k20|] 5
  False ← monadfn @[g1|k21|] 5
  False ← monadfn @[g1|k22|] 5
  False ← monadfn @[g1|k23|] 5
  False ← monadfn @[g1|k24|] 5
  False ← monadfn @[g1|k25|] 5
  False ← monadfn @[g1|k26|] 5
  False ← monadfn @[g1|k27|] 5
  True ← monadfn @[g1|k28|] 5
  True ← monadfn @[g1|k29|] 5
  True ← monadfn @[g1|k30|] 5
  return ()

{-# LANGUAGE AllowAmbiguousTypes #-}
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
{-# LANGUAGE ConstraintKinds #-}
-- {-# OPTIONS_GHC -dcore-lint #-}
-- {-# OPTIONS_GHC -ddump-tc-trace -ddump-to-file #-}
{-# OPTIONS_GHC -fplugin InversionOfControl.TcPlugin #-}

module Main where

import Data.Kind
import InversionOfControl.Lift
import InversionOfControl.MonadFn
import InversionOfControl.TypeDict

data Even
data Odd

instance MonadFn0 (Explicit Int Bool Even) IO where
  monadfn0 = return . even

instance MonadFn0 (Explicit Int Bool Odd) IO where
  monadfn0 = return . odd

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
      :+: Name "k28" Even
      :+: Name "k29" Even
      :+: Name "k30" Even
      :+: End

main ∷ IO ()
main = hardToCompileFn @OptionsD

data HardToCompileFnA (d ∷ Type)
type instance
  Definition (HardToCompileFnA d) =
    Name "k01" (Inherit (Explicit Int Bool) [k|k01|])
      :+: Name "k02" (Inherit (Explicit Int Bool) [k|k02|])
      :+: Name "k03" (Inherit (Explicit Int Bool) [k|k03|])
      :+: Name "k04" (Inherit (Explicit Int Bool) [k|k04|])
      :+: Name "k05" (Inherit (Explicit Int Bool) [k|k05|])
      :+: Name "k06" (Inherit (Explicit Int Bool) [k|k06|])
      :+: Name "k07" (Inherit (Explicit Int Bool) [k|k07|])
      :+: Name "k08" (Inherit (Explicit Int Bool) [k|k08|])
      :+: Name "k09" (Inherit (Explicit Int Bool) [k|k09|])
      :+: Name "k10" (Inherit (Explicit Int Bool) [k|k10|])
      :+: Name "k11" (Inherit (Explicit Int Bool) [k|k11|])
      :+: Name "k12" (Inherit (Explicit Int Bool) [k|k12|])
      :+: Name "k13" (Inherit (Explicit Int Bool) [k|k13|])
      :+: Name "k14" (Inherit (Explicit Int Bool) [k|k14|])
      :+: Name "k15" (Inherit (Explicit Int Bool) [k|k15|])
      :+: Name "k16" (Inherit (Explicit Int Bool) [k|k16|])
      :+: Name "k17" (Inherit (Explicit Int Bool) [k|k17|])
      :+: Name "k18" (Inherit (Explicit Int Bool) [k|k18|])
      :+: Name "k19" (Inherit (Explicit Int Bool) [k|k19|])
      :+: Name "k20" (Inherit (Explicit Int Bool) [k|k20|])
      :+: Name "k21" (Inherit (Explicit Int Bool) [k|k21|])
      :+: Name "k22" (Inherit (Explicit Int Bool) [k|k22|])
      :+: Name "k23" (Inherit (Explicit Int Bool) [k|k23|])
      :+: Name "k24" (Inherit (Explicit Int Bool) [k|k24|])
      :+: Name "k25" (Inherit (Explicit Int Bool) [k|k25|])
      :+: Name "k26" (Inherit (Explicit Int Bool) [k|k26|])
      :+: Name "k27" (Inherit (Explicit Int Bool) [k|k27|])
      :+: Name "k28" (Inherit (Explicit Int Bool) [k|k28|])
      :+: Name "k29" (Inherit (Explicit Int Bool) [k|k29|])
      :+: Name "k30" (Inherit (Explicit Int Bool) [k|k30|])
      :+: End

type HardToCompileFnD (d1 ∷ Type) =
  ( MonadFn [g1|k01|] IO
  , MonadFn [g1|k02|] IO
  , MonadFn [g1|k03|] IO
  , MonadFn [g1|k04|] IO
  , MonadFn [g1|k05|] IO
  , MonadFn [g1|k06|] IO
  , MonadFn [g1|k07|] IO
  , MonadFn [g1|k08|] IO
  , MonadFn [g1|k09|] IO
  , MonadFn [g1|k10|] IO
  , MonadFn [g1|k11|] IO
  , MonadFn [g1|k12|] IO
  , MonadFn [g1|k13|] IO
  , MonadFn [g1|k14|] IO
  , MonadFn [g1|k15|] IO
  , MonadFn [g1|k16|] IO
  , MonadFn [g1|k17|] IO
  , MonadFn [g1|k18|] IO
  , MonadFn [g1|k19|] IO
  , MonadFn [g1|k20|] IO
  , MonadFn [g1|k21|] IO
  , MonadFn [g1|k22|] IO
  , MonadFn [g1|k23|] IO
  , MonadFn [g1|k24|] IO
  , MonadFn [g1|k25|] IO
  , MonadFn [g1|k26|] IO
  , MonadFn [g1|k27|] IO
  , MonadFn [g1|k28|] IO
  , MonadFn [g1|k29|] IO
  , MonadFn [g1|k30|] IO
  ) :: Constraint

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
  False ← monadfn @[g1|k28|] 5
  False ← monadfn @[g1|k29|] 5
  False ← monadfn @[g1|k30|] 5
  return ()

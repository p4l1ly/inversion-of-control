{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
-- debug
-- {-# OPTIONS_GHC -dcore-lint #-}
-- {-# OPTIONS_GHC -ddump-tc-trace -ddump-to-file #-}
{-# OPTIONS_GHC -fplugin InversionOfControl.TcPlugin #-}
-- {-# OPTIONS_GHC -fplugin-opt InversionOfControl.TcPlugin:no_getK_singletonDataCon #-}

module Main where

import InversionOfControl.Lift (K (K), Mk, Pean (Zero), Wrap)
import InversionOfControl.MonadFn (Explicit, MonadFn (monadfn))
import InversionOfControl.TypeDict (Named (Name), ToConstraint, TypeDict (End, (:+:)), d, d')

data Even
data Odd

instance MonadFn ( 'K Zero (Explicit Int Bool Even)) IO where
  monadfn = return . even

instance MonadFn ( 'K Zero (Explicit Int Bool Odd)) IO where
  monadfn = return . odd

main :: IO ()
main =
  mazyFunction
    @( Name "k01" (Wrap Even)
        :+: Name "k02" (Wrap Even)
        :+: Name "k03" (Wrap Even)
        :+: Name "k04" (Wrap Even)
        :+: Name "k05" (Wrap Even)
        :+: Name "k06" (Wrap Even)
        :+: Name "k07" (Wrap Even)
        :+: Name "k08" (Wrap Even)
        :+: Name "k09" (Wrap Even)
        :+: Name "k10" (Wrap Even)
        :+: Name "k11" (Wrap Even)
        :+: Name "k12" (Wrap Even)
        :+: Name "k13" (Wrap Even)
        :+: Name "k14" (Wrap Even)
        :+: Name "k15" (Wrap Even)
        :+: Name "k16" (Wrap Even)
        :+: Name "k17" (Wrap Even)
        :+: Name "k18" (Wrap Even)
        :+: Name "k19" (Wrap Even)
        :+: Name "k20" (Wrap Even)
        :+: Name "k21" (Wrap Even)
        :+: Name "k22" (Wrap Even)
        :+: Name "k23" (Wrap Even)
        :+: Name "k24" (Wrap Even)
        :+: Name "k25" (Wrap Even)
        :+: Name "k26" (Wrap Even)
        :+: Name "k27" (Wrap Even)
        :+: Name "k28" (Wrap Even)
        :+: Name "k29" (Wrap Even)
        :+: Name "k30" (Wrap Even)
        :+: End
     )

mazyFunction ::
  forall d d'.
  ( d'
      ~ ( Name "k01" (Mk (Explicit Int Bool) [d|k01|])
            :+: Name "k02" (Mk (Explicit Int Bool) [d|k02|])
            :+: Name "k03" (Mk (Explicit Int Bool) [d|k03|])
            :+: Name "k04" (Mk (Explicit Int Bool) [d|k04|])
            :+: Name "k05" (Mk (Explicit Int Bool) [d|k05|])
            :+: Name "k06" (Mk (Explicit Int Bool) [d|k06|])
            :+: Name "k07" (Mk (Explicit Int Bool) [d|k07|])
            :+: Name "k08" (Mk (Explicit Int Bool) [d|k08|])
            :+: Name "k09" (Mk (Explicit Int Bool) [d|k09|])
            :+: Name "k10" (Mk (Explicit Int Bool) [d|k10|])
            :+: Name "k11" (Mk (Explicit Int Bool) [d|k11|])
            :+: Name "k12" (Mk (Explicit Int Bool) [d|k12|])
            :+: Name "k13" (Mk (Explicit Int Bool) [d|k13|])
            :+: Name "k14" (Mk (Explicit Int Bool) [d|k14|])
            :+: Name "k15" (Mk (Explicit Int Bool) [d|k15|])
            :+: Name "k16" (Mk (Explicit Int Bool) [d|k16|])
            :+: Name "k17" (Mk (Explicit Int Bool) [d|k17|])
            :+: Name "k18" (Mk (Explicit Int Bool) [d|k18|])
            :+: Name "k19" (Mk (Explicit Int Bool) [d|k19|])
            :+: Name "k20" (Mk (Explicit Int Bool) [d|k20|])
            :+: Name "k21" (Mk (Explicit Int Bool) [d|k21|])
            :+: Name "k22" (Mk (Explicit Int Bool) [d|k22|])
            :+: Name "k23" (Mk (Explicit Int Bool) [d|k23|])
            :+: Name "k24" (Mk (Explicit Int Bool) [d|k24|])
            :+: Name "k25" (Mk (Explicit Int Bool) [d|k25|])
            :+: Name "k26" (Mk (Explicit Int Bool) [d|k26|])
            :+: Name "k27" (Mk (Explicit Int Bool) [d|k27|])
            :+: Name "k28" (Mk (Explicit Int Bool) [d|k28|])
            :+: Name "k29" (Mk (Explicit Int Bool) [d|k29|])
            :+: Name "k30" (Mk (Explicit Int Bool) [d|k30|])
            :+: End
        )
  , ToConstraint
      ( Name "k01" (MonadFn [d'|k01|] IO)
          :+: Name "k02" (MonadFn [d'|k02|] IO)
          :+: Name "k03" (MonadFn [d'|k03|] IO)
          :+: Name "k04" (MonadFn [d'|k04|] IO)
          :+: Name "k05" (MonadFn [d'|k05|] IO)
          :+: Name "k06" (MonadFn [d'|k06|] IO)
          :+: Name "k07" (MonadFn [d'|k07|] IO)
          :+: Name "k08" (MonadFn [d'|k08|] IO)
          :+: Name "k09" (MonadFn [d'|k09|] IO)
          :+: Name "k10" (MonadFn [d'|k10|] IO)
          :+: Name "k11" (MonadFn [d'|k11|] IO)
          :+: Name "k12" (MonadFn [d'|k12|] IO)
          :+: Name "k13" (MonadFn [d'|k13|] IO)
          :+: Name "k14" (MonadFn [d'|k14|] IO)
          :+: Name "k15" (MonadFn [d'|k15|] IO)
          :+: Name "k16" (MonadFn [d'|k16|] IO)
          :+: Name "k17" (MonadFn [d'|k17|] IO)
          :+: Name "k18" (MonadFn [d'|k18|] IO)
          :+: Name "k19" (MonadFn [d'|k19|] IO)
          :+: Name "k20" (MonadFn [d'|k20|] IO)
          :+: Name "k21" (MonadFn [d'|k21|] IO)
          :+: Name "k22" (MonadFn [d'|k22|] IO)
          :+: Name "k23" (MonadFn [d'|k23|] IO)
          :+: Name "k24" (MonadFn [d'|k24|] IO)
          :+: Name "k25" (MonadFn [d'|k25|] IO)
          :+: Name "k26" (MonadFn [d'|k26|] IO)
          :+: Name "k27" (MonadFn [d'|k27|] IO)
          :+: Name "k28" (MonadFn [d'|k28|] IO)
          :+: Name "k29" (MonadFn [d'|k29|] IO)
          :+: Name "k30" (MonadFn [d'|k30|] IO)
          :+: End
      )
  ) =>
  IO ()
mazyFunction = do
  False <- [d'|monadfn|k01|] 5
  False <- [d'|monadfn|k02|] 5
  False <- [d'|monadfn|k03|] 5
  False <- [d'|monadfn|k04|] 5
  False <- [d'|monadfn|k05|] 5
  False <- [d'|monadfn|k06|] 5
  False <- [d'|monadfn|k07|] 5
  False <- [d'|monadfn|k08|] 5
  False <- [d'|monadfn|k09|] 5
  False <- [d'|monadfn|k10|] 5
  False <- [d'|monadfn|k11|] 5
  False <- [d'|monadfn|k12|] 5
  False <- [d'|monadfn|k13|] 5
  False <- [d'|monadfn|k14|] 5
  False <- [d'|monadfn|k15|] 5
  False <- [d'|monadfn|k16|] 5
  False <- [d'|monadfn|k17|] 5
  False <- [d'|monadfn|k18|] 5
  False <- [d'|monadfn|k19|] 5
  False <- [d'|monadfn|k20|] 5
  False <- [d'|monadfn|k21|] 5
  False <- [d'|monadfn|k22|] 5
  False <- [d'|monadfn|k23|] 5
  False <- [d'|monadfn|k24|] 5
  False <- [d'|monadfn|k25|] 5
  False <- [d'|monadfn|k26|] 5
  False <- [d'|monadfn|k27|] 5
  False <- [d'|monadfn|k28|] 5
  False <- [d'|monadfn|k29|] 5
  False <- [d'|monadfn|k30|] 5
  return ()

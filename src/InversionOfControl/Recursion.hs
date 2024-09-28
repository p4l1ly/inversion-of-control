{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UnicodeSyntax #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# OPTIONS_GHC -fplugin InversionOfControl.TcPlugin #-}
{-# OPTIONS_GHC -ddump-tc-trace -ddump-to-file #-}

module InversionOfControl.Recursion where

import GHC.TypeLits (Symbol)
import Data.Kind
import Control.Monad.Reader
import InversionOfControl.TypeDict
import InversionOfControl.MonadFn
import InversionOfControl.Lift
import InversionOfControl.LiftN

class Monad [fk|m|] ⇒ Recur k d where
  recur ::
    ([f|p|] -> [f|r|] -> [f|a|] -> [f|b|])
    -> [fk|c|] x
    -> [fk|m|] x

data AskRun (m :: Type -> Type)
data RecurD (name :: Symbol) d drest
type instance Definition (RecurD name d drest) =
  Name name (AskRun [fk|m|])
  :+: Follow (LiftUp drest)

instance
  ( LiftN n (ReaderT (p -> r -> bm bx) m) bm
  , Monad bm
  , Monad m
  ) => MonadFnN (E (K n (AskRun m)) (p, r) bx bm) where
  monadfnn (p, r) = do
    rec <- liftn @n ask
    rec p r

cata :: forall k d x. (Recur k d, [f|p|] ~ ()) => ([f|a|] -> [f|b|]) -> [fk|c|] x -> [fk|m|] x
cata algebra act = recur @k @d (\_ _ -> algebra) act

cataRec :: forall e r. (MonadFnN e, A e ~ ((), r)) => r -> M e (B e)
cataRec r = monadfnn @e ((), r)

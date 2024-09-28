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

module InversionOfControl.Recursion where

import Data.Kind

data E (k :: Type) (p :: Type) (r :: Type) (a :: Type) (b :: Type) (m2 :: Type -> Type) (m :: Type -> Type)

type family P e :: Type where
  P (E _ p _ _ _ _ _) = p
type family R e :: Type where
  R (E _ _ r _ _ _ _) = r
type family A e :: Type where
  A (E _ _ _ a _ _ _) = a
type family B e :: Type where
  B (E _ _ _ _ b _ _) = b
type family M2 e :: Type -> Type where
  M2 (E _ _ _ _ _ m2 _) = m2
type family M e :: Type -> Type where
  M (E _ _ _ _ _ _ m) = m

class Monad (M e) ⇒ Recur e where
  recur
    :: ((P e -> R e -> B e) -> P e -> R e -> A e -> B e)
    -> ((P e -> R e -> B e) -> M2 e a)
    -> M e a

cata :: forall e a. (Recur e, P e ~ ()) =>
  ((R e -> B e) -> A e -> B e)
  -> ((R e -> B e) -> M2 e a)
  -> M e a
cata algebra act = recur @e (\rec _ _ -> algebra (rec ())) (\rec -> act (rec ()))

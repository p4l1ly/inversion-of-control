{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UnicodeSyntax #-}

module InversionOfControl.MapRecur where

import Control.Monad.Trans
import Data.Kind
import InversionOfControl.Lift
import InversionOfControl.LiftN

data Explicit (k ∷ K) (r ∷ Type) (r' ∷ Type) (f ∷ Type)
type family Er e ∷ Type where
  Er (Explicit _ r _ _) = r
type family Er' e ∷ Type where
  Er' (Explicit _ _ r' _) = r'
type family Ef e ∷ Type where
  Ef (Explicit _ _ _ f) = f

type family Et (e ∷ Type) ∷ (Type → Type) → Type → Type

class (Monad m, MonadTrans (Et e), Monad (Et e m)) ⇒ Recur e m where
  runRecur ∷ Ef e → ((Er e → Et e m (Er' e)) → Et e m a) → m a

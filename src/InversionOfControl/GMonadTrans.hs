{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeOperators #-}

module InversionOfControl.GMonadTrans where

import Data.Kind
import Control.Monad.Trans

type family Unlift (t :: Type -> Type) :: Type -> Type

class (Monad t, Monad (Unlift t)) => GMonadTrans t where
  glift :: Unlift t a -> t a

instance (MonadTrans t, m ~ Unlift (t m), Monad m) => GMonadTrans (t m) where
  glift = lift

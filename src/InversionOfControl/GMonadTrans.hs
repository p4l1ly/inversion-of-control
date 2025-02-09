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
import Control.Monad.Reader (ReaderT)

type family Unlift (t :: Type -> Type) :: Type -> Type
type instance Unlift (ReaderT _ m) = m

class GMonadTrans t where
  glift :: Unlift t a -> t a

instance (MonadTrans t, m ~ Unlift (t m), Monad m) => GMonadTrans (t m) where
  glift = lift

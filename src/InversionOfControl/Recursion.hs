{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module InversionOfControl.Recursion where

import InversionOfControl.TypeDict
import qualified InversionOfControl.KFn as K
import InversionOfControl.Lift
import InversionOfControl.GMonadTrans
import Data.Kind

type TMB = (Type -> Type) -> Type -> Type

data E k p r a (mb :: TMB) xb
type family Algebra e (m0 :: Type -> Type)
type family MonadT e (m0 :: Type -> Type) :: Type -> Type

class Recursion e m0 where
  runRecursion :: MonadT e m0 c -> Algebra e m0 -> m0 c

type family BasicRecursionC e m0 :: Constraint where
  BasicRecursionC (E k p r a mb xb) m0 =
    ( Recursion (E k p r a mb xb) m0
    , Algebra (E k p r a mb xb) m0 ~ (p -> r -> a -> mb m0 xb)
    )

type RecE nb k p r mb (m0 :: Type -> Type) xb = K.E (K nb k) (p -> r -> mb m0 xb)

cata :: forall e r b. (K.KFn e, K.EKfn e ~ (() -> r -> b)) => r -> b
cata = K.kfn @e ()

-- RecurMonad1 ------------------------------------------------------------------------------------

type TType = TMB -> Type -> (Type -> Type) -> Type -> Type

newtype RecurMonad1 (t :: TType) xb (m0 :: Type -> Type) x
 = RecurMonad1 { unRecurMonad1 :: t (RecurMonad1 t xb) xb m0 x }

deriving newtype instance Functor (t (RecurMonad1 t xb) xb m0) => Functor (RecurMonad1 t xb m0)
deriving newtype instance Applicative (t (RecurMonad1 t xb) xb m0) => Applicative (RecurMonad1 t xb m0)
deriving newtype instance Monad (t (RecurMonad1 t xb) xb m0) => Monad (RecurMonad1 t xb m0)

type instance Unlift (RecurMonad1 t xb m0) = t (RecurMonad1 t xb) xb m0
instance {-# OVERLAPS #-}
  Monad (t (RecurMonad1 t xb) xb m0) => GMonadTrans (RecurMonad1 t xb m0) where
  glift = RecurMonad1

type family E1 k p r a (t :: TType) xb :: Type where
  E1 k p r a t xb = E k p r a (RecurMonad1 t xb) xb

type family BasicRecursion1C e (m0 :: Type -> Type) :: Constraint where
  BasicRecursion1C (E k p r a (RecurMonad1 t xb) xb) m0 =
    ( BasicRecursionC (E k p r a (RecurMonad1 t xb) xb) m0
    , MonadT (E k p r a (RecurMonad1 t xb) xb) m0 ~ t (RecurMonad1 t xb) xb m0
    )

-- RecurMonad2 ------------------------------------------------------------------------------------

-- newtype RecurMonad2
--   (t2 :: (Type -> Type) -> Type -> (Type -> Type) -> Type -> Type)
--   (xb2 :: Type)
--   (t1 :: (Type -> Type) -> Type -> (Type -> Type) -> Type -> Type)
--   (xb1 :: Type)
--   (m0 :: Type -> Type)
--   (x :: Type)
--  = RecurMonad2
--   { unRecurMonad2 ::
--       t2 (RecurMonad2 t2 xb2 t1 xb1 m0) xb2 (t1 (RecurMonad2 t2 xb2 t1 xb1 m0) xb1 m0) x
--   }
-- 
-- deriving newtype instance
--   Functor (t2 (RecurMonad2 t2 xb2 t1 xb1 m0) xb2 (t1 (RecurMonad2 t2 xb2 t1 xb1 m0) xb1 m0))
--   => Functor (RecurMonad2 t2 xb2 t1 xb1 m0)
-- deriving newtype instance
--   Applicative (t2 (RecurMonad2 t2 xb2 t1 xb1 m0) xb2 (t1 (RecurMonad2 t2 xb2 t1 xb1 m0) xb1 m0))
--   => Applicative (RecurMonad2 t2 xb2 t1 xb1 m0)
-- deriving newtype instance
--   Monad (t2 (RecurMonad2 t2 xb2 t1 xb1 m0) xb2 (t1 (RecurMonad2 t2 xb2 t1 xb1 m0) xb1 m0))
--   => Monad (RecurMonad2 t2 xb2 t1 xb1 m0)
-- 
-- type instance Unlift (RecurMonad2 t2 xb2 t1 xb1 m0) =
--   t2 (RecurMonad2 t2 xb2 t1 xb1 m0) xb2 (t1 (RecurMonad2 t2 xb2 t1 xb1 m0) xb1 m0)
-- instance {-# OVERLAPS #-}
--   Monad (t2 (RecurMonad2 t2 xb2 t1 xb1 m0) xb2 (t1 (RecurMonad2 t2 xb2 t1 xb1 m0) xb1 m0))
--   => GMonadTrans (RecurMonad2 t2 xb2 t1 xb1 m0) where
--   glift = RecurMonad2

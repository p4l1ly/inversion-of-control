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
import InversionOfControl.KFn
import InversionOfControl.Lift
import InversionOfControl.GMonadTrans
import Data.Kind

type family Algebra k p r a (mb :: Type -> Type) xb
type family MonadT k p r a (mb :: Type -> Type) xb (m0 :: Type -> Type) c :: Type

class Recursion k p r a mb xb m0 c where
  runRecursion :: MonadT k p r a mb xb m0 c -> Algebra k p r a mb xb -> m0 c

type BasicRecursionC k p r a mb xb m0 c =
  ( Recursion k p r a mb xb m0 c
  , Algebra k p r a mb xb ~ (p -> r -> a -> mb xb)
  ) :: Constraint
type CataC k r a mb xb m0 c = BasicRecursionC k () r a mb xb m0 c

type RecE nb k p r mb xb = E (K nb k) (p -> r -> mb xb)

cata :: forall e r b. (KFn e, EKfn e ~ (() -> r -> b)) => r -> b
cata = kfn @e ()

-- RecurMonad1 ------------------------------------------------------------------------------------

type BasicRecursion1C k p r a t xb m0 c =
  ( BasicRecursionC k p r a (RecurMonad1 t xb m0) xb m0 c
  , MonadT k p r a (RecurMonad1 t xb m0) xb m0 c ~ t (RecurMonad1 t xb m0) xb m0 c
  ) :: Constraint
type Cata1C k r a t xb m0 c = BasicRecursion1C k () r a t xb m0 c

newtype RecurMonad1
  (t :: (Type -> Type) -> Type -> (Type -> Type) -> Type -> Type)
  (xb :: Type)
  (m0 :: Type -> Type)
  (x :: Type)
 = RecurMonad1 { unRecurMonad1 :: t (RecurMonad1 t xb m0) xb m0 x }

deriving newtype instance Functor (t (RecurMonad1 t xb m0) xb m0) => Functor (RecurMonad1 t xb m0)
deriving newtype instance Applicative (t (RecurMonad1 t xb m0) xb m0) => Applicative (RecurMonad1 t xb m0)
deriving newtype instance Monad (t (RecurMonad1 t xb m0) xb m0) => Monad (RecurMonad1 t xb m0)

type instance Unlift (RecurMonad1 t xb m0) = t (RecurMonad1 t xb m0) xb m0
instance {-# OVERLAPS #-}
  Monad (t (RecurMonad1 t xb m0) xb m0) => GMonadTrans (RecurMonad1 t xb m0) where
  glift = RecurMonad1

-- RecurMonad2 ------------------------------------------------------------------------------------

newtype RecurMonad2
  (t2 :: (Type -> Type) -> Type -> (Type -> Type) -> Type -> Type)
  (xb2 :: Type)
  (t1 :: (Type -> Type) -> Type -> (Type -> Type) -> Type -> Type)
  (xb1 :: Type)
  (m0 :: Type -> Type)
  (x :: Type)
 = RecurMonad2
  { unRecurMonad2 ::
      t2 (RecurMonad2 t2 xb2 t1 xb1 m0) xb2 (t1 (RecurMonad2 t2 xb2 t1 xb1 m0) xb1 m0) x
  }

deriving newtype instance
  Functor (t2 (RecurMonad2 t2 xb2 t1 xb1 m0) xb2 (t1 (RecurMonad2 t2 xb2 t1 xb1 m0) xb1 m0))
  => Functor (RecurMonad2 t2 xb2 t1 xb1 m0)
deriving newtype instance
  Applicative (t2 (RecurMonad2 t2 xb2 t1 xb1 m0) xb2 (t1 (RecurMonad2 t2 xb2 t1 xb1 m0) xb1 m0))
  => Applicative (RecurMonad2 t2 xb2 t1 xb1 m0)
deriving newtype instance
  Monad (t2 (RecurMonad2 t2 xb2 t1 xb1 m0) xb2 (t1 (RecurMonad2 t2 xb2 t1 xb1 m0) xb1 m0))
  => Monad (RecurMonad2 t2 xb2 t1 xb1 m0)

type instance Unlift (RecurMonad2 t2 xb2 t1 xb1 m0) =
  t2 (RecurMonad2 t2 xb2 t1 xb1 m0) xb2 (t1 (RecurMonad2 t2 xb2 t1 xb1 m0) xb1 m0)
instance {-# OVERLAPS #-}
  Monad (t2 (RecurMonad2 t2 xb2 t1 xb1 m0) xb2 (t1 (RecurMonad2 t2 xb2 t1 xb1 m0) xb1 m0))
  => GMonadTrans (RecurMonad2 t2 xb2 t1 xb1 m0) where
  glift = RecurMonad2

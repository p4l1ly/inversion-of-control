{-# LANGUAGE UnicodeSyntax #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE ImpredicativeTypes #-}
{-# OPTIONS_GHC -fplugin InversionOfControl.TcPlugin #-}

module Main where

import Data.Traversable
import Data.Semigroup
import GHC.TypeLits (Symbol)
import Control.Monad.Reader
import Data.IORef
import Data.Functor.Compose
import Data.Fix hiding (cata)
import Control.Monad.Free
-- import qualified InversionOfControl.Recursion.IORefGraph as RecIO
import qualified InversionOfControl.Recursion.Free as RecFree
import qualified InversionOfControl.Recursion.Fix as RecFix
import qualified InversionOfControl.Recursion.Pure as RecPure
import InversionOfControl.Recursion
import InversionOfControl.Lift
import InversionOfControl.TypeDict
import InversionOfControl.KFn
import InversionOfControl.GMonadTrans
import Data.Kind
import Data.Functor.Classes

data BoolFormula int bool =
  And bool bool
  | Not bool
  | Leq int int
  | BoolLit Bool
  deriving (Eq, Functor, Foldable, Traversable)

instance Show int => Show1 (BoolFormula int) where
  liftShowsPrec sp _ d = \case
    And a b -> showsBinaryWith sp sp "And" d a b
    Not a -> showsUnaryWith sp "Not" d a
    Leq a b -> showsBinaryWith showsPrec showsPrec "Leq" d a b
    BoolLit b -> showsUnaryWith showsPrec "BoolLit" d b

instance (Show int, Show bool) => Show (BoolFormula int bool) where
  show (And a b) = "(" ++ show a ++ " && " ++ show b ++ ")"
  show (Leq a b) = "(" ++ show a ++ " <= " ++ show b ++ ")"
  show (Not a) = "!" ++ show a
  show (BoolLit False) = "F"
  show (BoolLit True) = "T"

data IntFormula bool int =
  Count [bool]
  | Plus int int
  | IntLit Int
  deriving (Eq, Functor, Foldable, Traversable)

instance Show bool => Show1 (IntFormula bool) where
  liftShowsPrec sp s1 d = \case
    Count xs -> showsUnaryWith showsPrec "Count" d xs
    Plus a b -> showsBinaryWith sp sp "Plus" d a b
    IntLit i -> showsUnaryWith showsPrec "IntLit" d i

instance (Show int, Show bool) => Show (IntFormula int bool) where
  show (Count xs) = show xs
  show (Plus a b) = "(" ++ show a ++ " + " ++ show b ++ ")"
  show (IntLit i) = show i

fix1_val :: Bool -> Fix (BoolFormula Int)
fix1_val val = Fix $ And
  (Fix $ Not $ Fix $ And leq (Fix $ BoolLit val))
  (Fix $ And leq (Fix $ Not $ Fix $ BoolLit val))
  where leq = (Fix $ Leq 1 2)

fterm x = Right (Fix (Compose x))

fix1_var :: Fix (Compose (BoolFormula Int) (Either Word))
fix1_var = Fix $ Compose $ And
  (fterm $ Not $ fterm $ And leq (Left 0))
  (fterm $ And leq (fterm $ Not $ Left 0))
  where leq = (fterm $ Leq 1 2)

-- Free is just the same as Fix+Compose+Either (even in memory, as Fix and Compose are newtypes)
free1 :: Free (BoolFormula Int) Word
free1 = Free $ And
  (Free $ Not $ Free $ And leq (Pure 0))
  (Free $ And leq (Free $ Not $ Pure 0))
  where leq = (Free $ Leq 1 2)

-- term x = Right (Free (Compose x))
-- shared x = Right (Pure x)
-- 
-- iorefg1_val :: Bool -> IO (RecIO.RefFix (BoolFormula Int))
-- iorefg1_val val = do
--   leq <- RecIO.buildFoldable $ Leq 1 2
--   RecIO.buildFree $ Free $ And
--     (Free $ Not $ Free $ And (Pure leq) (Free $ BoolLit val))
--     (Free $ And (Pure leq) (Free $ Not $ Free $ BoolLit val))
-- 
-- iorefg1_var :: IO (RecIO.RefFix (Compose (BoolFormula Int) (Either Word)))
-- iorefg1_var = do
--   leq <- RecIO.buildFoldable $ Compose $ Leq 1 2
--   RecIO.buildFree $ Free $ Compose $ And
--     (term $ Not $ term $ And (shared leq) (Left 0))
--     (term $ And (shared leq) (term $ Not $ Left 0))

type CIO = ReaderT (IORef Int) IO

incCounter :: CIO ()
incCounter = do
  ref <- ask
  liftIO $ modifyIORef' ref (+1)

runCIO :: CIO a -> IO Int
runCIO act = do
  ref <- newIORef 0
  runReaderT act ref
  readIORef ref

-- boolShareCount
--   :: forall d m bool self.
--   ( Int ~ [f|bx|]
--   , Sum Int ~ [f|p|]
--   , [f|r|] ~ RecIO.RefFix [fk|f|]
--   , Monad [fk|m|]
--   ) => Sum Int
--   -> self
--   -> BoolFormula bool [f|r|]
--   -> RecIO.SemigroupA (RecIO.RecFixD d) Int
-- boolShareCount (Sum p) _ fr = RecIO.SemigroupA $ Compose do
--   let RecIO.SemigroupA (Compose bef) =
--         for fr \(RecIO.RefFix child) -> RecIO.SemigroupA $ Compose do
--           recur <- ask
--           let RecIO.SemigroupA (Compose bef) = recur (Sum 1) child
--           bef
--   aft <- bef
--   return do (fromEnum (p > 1) +) . sum <$> aft

type RecBool d m = [e|CataE|recBool|] [f|bool|] (BoolFormula [f|int|] [f|bool|]) (m Bool)
type RecInt d m = [e|CataE|recInt|] [f|int|] (IntFormula [f|bool|] [f|int|]) (m Int)
type RunCIO d m a = E [k|runCIO|] (CIO a -> m a)

type RecApp d m =
  ( Monad m
  , KFn (RecBool d m)
  , KFn (RecInt d m)
  , forall a. KFn (RunCIO d m a)
  , Show [f|bool|]
  , Show [f|int|]
  ) :: Constraint

recBool :: forall d m. RecApp d m => [f|bool|] -> m Bool
recBool = kfn @(RecBool d m) (boolAlgebra @d)

recInt :: forall d m. RecApp d m => [f|int|] -> m Int
recInt = kfn @(RecInt d m) (intAlgebra @d)

intAlgebra :: forall d m. RecApp d m => IntFormula [f|bool|] [f|int|] -> m Int
intAlgebra (Count xs) = do
  kfn @(RunCIO d _ _) incCounter
  args <- mapM (recBool @d) xs
  let result = sum $ map fromEnum args
  kfn @(RunCIO d _ _) $ lift do print ("[]", result, args, xs)
  return result
intAlgebra (Plus x y) = do
  args <- (,) <$> (recInt @d) x <*> (recInt @d) y
  let result = uncurry (+) args
  kfn @(RunCIO d _ _) $ lift do print ("++", result, args, x, y)
  return result
intAlgebra (IntLit i) = do
  kfn @(RunCIO d _ _) $ lift do print ("II", i)
  return i

boolAlgebra :: forall d m. RecApp d m => BoolFormula [f|int|] [f|bool|] -> m Bool
boolAlgebra (And x y) = do
  args <- (,) <$> (recBool @d) x <*> (recBool @d) y
  let result = uncurry (&&) args
  kfn @(RunCIO d _ _) $ lift do print ("&&", result, args, x, y)
  return result
boolAlgebra (Not x) = do
  args <- (recBool @d) x
  let result = not args
  kfn @(RunCIO d _ _) $ lift do print ("!!", result, args, x)
  return result
boolAlgebra (Leq x y) = do
  kfn @(RunCIO d _ _) incCounter
  args <- (,) <$> (recInt @d) x <*> (recInt @d) y
  let result = uncurry (<=) args
  kfn @(RunCIO d _ _) $ lift do print ("<=", result, args, x, y)
  return result
boolAlgebra (BoolLit b) = do
  kfn @(RunCIO d _ _) $ lift do print ("BB", b)
  return b

-- boolAlgebraVar ::
--   forall d m.
--   RecApp (VarD d) (ReaderT (Word -> Bool) m)
--   => (Word -> Bool)
--   -> Compose (BoolFormula [f|int|]) (Either Word) [f|bool|]
--   -> m Bool
-- boolAlgebraVar valuation (Compose fr) = runReaderT undefined valuation
-- 
-- data VarD d
-- type instance Definition (VarD d) =
--   Name "bool" (Either Word [f|bool|])
--   :+: Name "recBool" (Valuate [k|recBool|])
--   :+: Follow (LiftUp d)
-- 
-- data Valuate key
-- instance
--   ( Monad m
--   , KFn (E key (Recur p r a (m b)))
--   )
--   => MonadFn (E (K Zero (Valuate key)) ((p -> r -> a -> m b) -> p -> Either a r -> ReaderT (a -> b) m b)
--   where
--   monadfn (p, er) = case er of
--     Left x -> ($ x) <$> ask
--     Right r -> lift $ monadfnn @(E key (p, r) b m) (p, r)
-- 
-- instance
--   (Monad m, MonadFn (E (K n (Valuate key)) a b m)) =>
--   MonadFnN (E (K n (Valuate key)) a b m) where
--   monadfnn = monadfn @(E (K n (Valuate key)) a b m)


data D0
type instance Definition D0 =
  Name "runCIO" Lifter
  :+: Name "recBool" RecPure.Rec
  :+: Name "recInt" RecPure.Rec
  :+: Name "bool" Bool
  :+: Name "int" Int
  :+: End

data FixD
type instance Definition FixD =
  Name "recBool" RecFix.Rec
  :+: Name "bool" (Fix (BoolFormula Int))
  :+: Follow D0

data VarFixD
type instance Definition VarFixD =
  Name "recBool" RecFix.Rec
  :+: Name "bool" (Fix (Compose (BoolFormula Int) (Either Word)))
  :+: Follow D0

-- data D1_ d
-- type instance Definition (D1_ d) =
--   Name "refBool" [g|r|]
--   :+: Follow ([fk|recurd|] "recBool" d D0)

-- data D1 d
-- type instance Definition (D1 d) = Follow (LiftUp (D1_ d))

-- data D2_ d d1
-- type instance Definition (D2_ d d1) =
--   Name "refInt" [g|r|]
--   :+: Follow ([fk|recurd|] "recInt" d d1)

-- data D2 d d1
-- type instance Definition (D2 d d1) = Follow (LiftUp (D2_ d (D1_ d1)))

-- newtype RecM r b c = RecM {unRecM :: ReaderT (() -> r -> RecM r b b) CIO c}
--   deriving newtype (Functor, Applicative, Monad)
-- 
-- instance GMonadTrans (RecM r b) (ReaderT (() -> r -> RecM r b b) CIO) where
--   glift = RecM

-- data GenFixE (f :: Type -> Type)
-- type instance Definition (GenFixE f) =
--   Name "p" ()
--   :+: Name "f" (Kindy f)
--   :+: Name "r" (Fix f)
--   :+: Name "a" (f [gs|r|])
--   :+: Name "m" (Kindy CIO)
--   :+: Name "c" (Kindy (ReaderT (() -> [gs|r|] -> RecM [gs|r|] Bool Bool) CIO))
--   :+: Name "bm" (Kindy (RecM [gs|r|] Bool))
--   :+: Name "bx" Bool
--   :+: Name "b" ([fsk|bm|] [gs|bx|])
--   :+: Name "recurd" (Kindy RecurD)
--   :+: End
-- type FixE = GenFixE (BoolFormula Int)
-- type VFixE = GenFixE (Compose (BoolFormula Int) (Either Word))

-- data GenGraphE (f :: Type -> Type)
-- type instance Definition (GenGraphE f) =
--   Name "p" ()
--   :+: Name "f" (Kindy f)
--   :+: Name "r" (RecIO.RefFix f)
--   :+: Name "a" (f [gs|r|])
--   :+: Name "m" (Kindy CIO)
--   :+: Name "c" (Kindy (ReaderT (() -> RecIO.Ref (f (RecIO.RefFix f)) -> RecM (RecIO.Ref (f (RecIO.RefFix f))) Bool Bool) CIO))
--   :+: Name "bm" (Kindy (RecM (RecIO.Ref (f (RecIO.RefFix f))) Bool))
--   :+: Name "bx" Bool
--   :+: Name "b" ([fsk|bm|] [gs|bx|])
--   :+: Name "recurd" (Kindy RecIO.FixRecurD)
--   :+: End
-- type GraphE = GenGraphE (BoolFormula Int)
-- type VGraphE = GenGraphE (Compose (BoolFormula Int) (Either Word))
-- 
-- data SemigroupE
-- type instance Definition SemigroupE =
--   Name "p" (Sum Int)
--   :+: Name "f" (Kindy (BoolFormula Int))
--   :+: Name "r" (RecIO.RefFix (BoolFormula Int))
--   :+: Name "a" (BoolFormula Int [gs|r|])
--   :+: Name "m" (Kindy IO)
--   :+: Name "bx" Int
--   :+: Name "b" (RecIO.SemigroupA (RecIO.RecFixD SemigroupE) [gs|bx|])
--   :+: Name "c" (Kindy (RecIO.SemigroupA (RecIO.RecFixD SemigroupE)))
--   :+: End
-- 
-- data FreeE
-- type instance Definition FreeE =
--   Name "p" ()
--   :+: Name "f" (Kindy (BoolFormula Int))
--   :+: Name "r" (Free [fsk|f|] Bool)
--   :+: Name "a" ([fsk|f|] [gs|r|])
--   :+: Name "m" (Kindy CIO)
--   :+: Name "c" (Kindy (ReaderT (() -> [gs|r|] -> RecM [gs|r|] Bool Bool) CIO))
--   :+: Name "bm" (Kindy (RecM [gs|r|] Bool))
--   :+: Name "bx" Bool
--   :+: Name "b" ([fsk|bm|] [gs|bx|])
--   :+: Name "recurd" (Kindy RecurD)
--   :+: End
-- 
-- newtype BoolIntFormula = BoolIntFormula (BoolFormula IntBoolFormula BoolIntFormula)
--   deriving newtype Show
-- newtype IntBoolFormula = IntBoolFormula (IntFormula BoolIntFormula IntBoolFormula)
--   deriving newtype Show
-- 
-- data RecBoolInt
-- instance
--   ( Monad [fk|m|]
--   , [f|r|] ~ BoolIntFormula
--   , [f|a|] ~ BoolFormula IntBoolFormula BoolIntFormula
--   , [f|c|] ~ Kindy (ReaderT ([f|p|] -> [f|r|] -> [f|b|]) [fk|m|])
--   ) ⇒
--   Recur (K n RecBoolInt) d
--   where
--   recur algebra act = do
--     let rec p r@(BoolIntFormula fr) = algebra p r fr
--     runReaderT act rec
-- 
-- data RecIntBool
-- instance
--   ( Monad [fk|m|]
--   , [f|r|] ~ IntBoolFormula
--   , [f|a|] ~ IntFormula BoolIntFormula IntBoolFormula
--   , [f|c|] ~ Kindy (ReaderT ([f|p|] -> [f|r|] -> [f|b|]) [fk|m|])
--   ) ⇒
--   Recur (K n RecIntBool) d
--   where
--   recur algebra act = do
--     let rec p r@(IntBoolFormula fr) = algebra p r fr
--     runReaderT act rec
-- 
-- newtype BoolIntFormula' = BoolIntFormula' (BoolFormula (RecIO.Ref IntBoolFormula') (RecIO.Ref BoolIntFormula'))
-- newtype IntBoolFormula' = IntBoolFormula' (IntFormula (RecIO.Ref BoolIntFormula') (RecIO.Ref IntBoolFormula'))
-- 
-- data RecBoolInt' n
-- instance
--   ( Monad [fk|m|]
--   , [f|r|] ~ RecIO.Ref BoolIntFormula'
--   , [f|a|] ~ BoolFormula (RecIO.Ref IntBoolFormula') (RecIO.Ref BoolIntFormula')
--   , Recur (K n (RecIO.Rec n')) (RecBoolInt'D d)
--   ) =>
--   Recur (K n (RecBoolInt' n')) d
--   where
--   recur algebra act =
--     recur @(K n (RecIO.Rec n')) @(RecBoolInt'D d)
--       (\p r (BoolIntFormula' fr) -> algebra p r fr)
--       act
-- 
-- data RecBoolInt'D d
-- type instance Definition (RecBoolInt'D d) = Name "a" BoolIntFormula' :+: Follow d
-- 
-- data RecIntBool' n
-- instance
--   ( Monad [fk|m|]
--   , [f|r|] ~ RecIO.Ref IntBoolFormula'
--   , [f|a|] ~ IntFormula (RecIO.Ref BoolIntFormula') (RecIO.Ref IntBoolFormula')
--   , Recur (K n (RecIO.Rec n')) (RecIntBool'D d)
--   ) =>
--   Recur (K n (RecIntBool' n')) d
--   where
--   recur algebra act =
--     recur @(K n (RecIO.Rec n')) @(RecIntBool'D d)
--       (\p r (IntBoolFormula' fr) -> algebra p r fr)
--       act
-- 
-- data RecIntBool'D d
-- type instance Definition (RecIntBool'D d) = Name "a" IntBoolFormula' :+: Follow d
-- 
-- type RecM2In1 r1 r2 b1 b2 = ReaderT (() -> r1 -> RecM2 r1 r2 b1 b2 b1) CIO
-- type RecM2In2 r1 r2 b1 b2 = ReaderT (() -> r2 -> RecM2 r1 r2 b1 b2 b2) (RecM2In1 r1 r2 b1 b2)
-- 
-- newtype RecM2 r1 r2 b1 b2 c = RecM2
--   {unRecM2 :: RecM2In2 r1 r2 b1 b2 c}
--   deriving newtype (Functor, Applicative, Monad)
-- 
-- instance GMonadTrans (RecM2 r1 r2 b1 b2) (RecM2In2 r1 r2 b1 b2) where
--   glift = RecM2
-- 
-- data BoolIntE
-- type instance Definition BoolIntE =
--   Name "p" ()
--   :+: Name "r" BoolIntFormula
--   :+: Name "a" (BoolFormula IntBoolFormula BoolIntFormula)
--   :+: Name "m" (Kindy CIO)
--   :+: Name "bx" Bool
--   :+: Name "bm" (Kindy (RecM2 BoolIntFormula IntBoolFormula Bool Int))
--   :+: Name "b" ([fsk|bm|] [gs|bx|])
--   :+: Name "c" (Kindy (RecM2In1 BoolIntFormula IntBoolFormula Bool Int))
--   :+: Name "recurd" (Kindy RecurD)
--   :+: End
-- 
-- data IntBoolE
-- type instance Definition IntBoolE =
--   Name "p" ()
--   :+: Name "r" IntBoolFormula
--   :+: Name "a" (IntFormula BoolIntFormula IntBoolFormula)
--   :+: Name "m" (Kindy (RecM2In1 BoolIntFormula IntBoolFormula Bool Int))
--   :+: Name "bx" Int
--   :+: Name "bm" (Kindy (RecM2 BoolIntFormula IntBoolFormula Bool Int))
--   :+: Name "b" ([fsk|bm|] [gs|bx|])
--   :+: Name "c" (Kindy (RecM2In2 BoolIntFormula IntBoolFormula Bool Int))
--   :+: Name "recurd" (Kindy RecurD)
--   :+: End
-- 
-- data BoolInt'E
-- type instance Definition BoolInt'E =
--   Name "p" ()
--   :+: Name "r" (RecIO.Ref BoolIntFormula')
--   :+: Name "a" (BoolFormula (RecIO.Ref IntBoolFormula') (RecIO.Ref BoolIntFormula'))
--   :+: Name "m" (Kindy CIO)
--   :+: Name "bx" Bool
--   :+: Name "bm" (Kindy (RecM2 (RecIO.Ref BoolIntFormula') (RecIO.Ref IntBoolFormula') Bool Int))
--   :+: Name "b" ([fsk|bm|] [gs|bx|])
--   :+: Name "c" (Kindy (RecM2In1 (RecIO.Ref BoolIntFormula') (RecIO.Ref IntBoolFormula') Bool Int))
--   :+: Name "recurd" (Kindy RecurD)
--   :+: End
-- 
-- data IntBool'E
-- type instance Definition IntBool'E =
--   Name "p" ()
--   :+: Name "r" (RecIO.Ref IntBoolFormula')
--   :+: Name "a" (IntFormula (RecIO.Ref BoolIntFormula') (RecIO.Ref IntBoolFormula'))
--   :+: Name "m" (Kindy (RecM2In1 (RecIO.Ref BoolIntFormula') (RecIO.Ref IntBoolFormula') Bool Int))
--   :+: Name "bx" Int
--   :+: Name "bm" (Kindy (RecM2 (RecIO.Ref BoolIntFormula') (RecIO.Ref IntBoolFormula') Bool Int))
--   :+: Name "b" ([fsk|bm|] [gs|bx|])
--   :+: Name "c" (Kindy (RecM2In2 (RecIO.Ref BoolIntFormula') (RecIO.Ref IntBoolFormula') Bool Int))
--   :+: Name "recurd" (Kindy RecurD)
--   :+: End
-- 
-- fix2 :: Bool -> Bool -> BoolIntFormula
-- fix2 val1 val2 = BoolIntFormula $ And
--   (BoolIntFormula $ Not $ BoolIntFormula $ And leq (BoolIntFormula $ BoolLit val1))
--   (BoolIntFormula $ And leq (BoolIntFormula $ Not $ BoolIntFormula $ BoolLit val1))
--   where
--     leq = BoolIntFormula $ Leq count2 (IntBoolFormula $ IntLit 2)
--     count = IntBoolFormula $ Count [tv2, BoolIntFormula $ BoolLit True, tv2]
--     count2 = IntBoolFormula $ Plus count count
--     tv2 = BoolIntFormula $ And (BoolIntFormula $ BoolLit True) (BoolIntFormula $ BoolLit val2)
-- 
-- iorefg2 :: Bool -> Bool -> IO (RecIO.Ref BoolIntFormula')
-- iorefg2 val1 val2 = do
--   v2 <- RecIO.buildTopo 0 $ BoolIntFormula' $ BoolLit val2
--   print ("v2", v2)
--   t <- RecIO.buildTopo 0 $ BoolIntFormula' $ BoolLit True
--   print ("t", t)
--   tv2 <- RecIO.buildTopo 1 $ BoolIntFormula' $ And t v2
--   print ("tv2", tv2)
--   count <- RecIO.buildTopo 2 $ IntBoolFormula' $ Count [tv2, t, tv2]
--   print ("count", count)
--   plus <- RecIO.buildTopo 3 $ IntBoolFormula' $ Plus count count
--   print ("plus", plus)
--   l1 <- RecIO.buildTopo 0 $ IntBoolFormula' $ IntLit 2
--   print ("l1", l1)
--   leq <- RecIO.buildTopo 3 $ BoolIntFormula' $ Leq plus l1
--   print ("leq", leq)
--   v1 <- RecIO.buildTopo 0 $ BoolIntFormula' $ BoolLit val1
--   print ("v1", v1)
--   nv1 <- RecIO.buildTopo 1 $ BoolIntFormula' $ Not v1
--   print ("nv1", nv1)
--   leqv1 <- RecIO.buildTopo 4 $ BoolIntFormula' $ And leq v1
--   print ("leqv1", leqv1)
--   leqnv1 <- RecIO.buildTopo 4 $ BoolIntFormula' $ And leq nv1
--   print ("leqnv1", leqnv1)
--   nleqv1 <- RecIO.buildTopo 5 $ BoolIntFormula' $ Not leqv1
--   print ("nleqv1", nleqv1)
--   RecIO.buildTopo 6 $ BoolIntFormula' $ And nleqv1 leqnv1

main ∷ IO ()
main = do
  -- Test the algebrae

  2 <- runCIO do
    False <- boolAlgebra @D0 $ And True False 
    True <- boolAlgebra @D0 $ Not False
    True <- boolAlgebra @D0 $ Leq 1 2
    False <- boolAlgebra @D0 $ BoolLit False
    3 <- intAlgebra @D0 $ Count [False, True, True, False, True]
    5 <- intAlgebra @D0 $ Plus 3 2
    9 <- intAlgebra @D0 $ IntLit 9
    return ()

  -- Test recursion of Fix

  2 <- runCIO do
    False <- recBool @FixD $ fix1_val True
    return ()

  2 <- runCIO do
    True <- recBool @FixD $ fix1_val False
    return ()

  -- 2 <- runCIO do
  --   False <- cata @(K Zero RecFix.Rec) @VFixE
  --     (boolAlgebraVar @(D1 VFixE) (\0 -> True))
  --     (unRecM $ cataRec @(RecBool (D1 VFixE) _ _) $ fix1_var)
  --   return ()

  -- 2 <- runCIO do
  --   True <- cata @(K Zero RecFix.Rec) @VFixE
  --     (boolAlgebraVar @(D1 VFixE) (\0 -> False))
  --     (unRecM $ cataRec @(RecBool (D1 VFixE) _ _) $ fix1_var)
  --   return ()

  -- -- Test recursion of Free

  -- 2 <- runCIO do
  --   False <- cata @(K Zero RecFree.Rec) @FreeE
  --     (boolAlgebra @(D1 FreeE))
  --     (unRecM $ cataRec @(RecBool (D1 FreeE) _ _) $ fmap (\0 -> True) free1)
  --   return ()

  -- 2 <- runCIO do
  --   True <- cata @(K Zero RecFree.Rec) @FreeE
  --     (boolAlgebra @(D1 FreeE))
  --     (unRecM $ cataRec @(RecBool (D1 FreeE) _ _) $ fmap (\0 -> False) free1)
  --   return ()

  -- -- Test recursion of IORefGraph

  -- iorefg1_True <- iorefg1_val True
  -- 1 <- runCIO do
  --   False <- cata @(K (Succ Zero) (RecIO.RecFix (Succ Zero))) @GraphE
  --     (boolAlgebra @(D1 GraphE))
  --     (unRecM $ cataRec @(RecBool (D1 GraphE) _ _) $ iorefg1_True)
  --   return ()

  -- iorefg1_False <- iorefg1_val False
  -- 1 <- runCIO do
  --   True <- cata @(K (Succ Zero) (RecIO.RecFix (Succ Zero))) @GraphE
  --     (boolAlgebra @(D1 GraphE))
  --     (unRecM $ cataRec @(RecBool (D1 GraphE) _ _) $ iorefg1_False)
  --   return ()

  -- iorefg1_var' <- iorefg1_var
  -- 1 <- runCIO do
  --   False <- cata @(K (Succ Zero) (RecIO.RecFix (Succ Zero))) @VGraphE
  --     (boolAlgebraVar @(D1 VGraphE) (\0 -> True))
  --     (unRecM $ cataRec @(RecBool (D1 VGraphE) _ _) $ iorefg1_var')
  --   return ()

  -- 1 <- runCIO do
  --   True <- cata @(K (Succ Zero) (RecIO.RecFix (Succ Zero))) @VGraphE
  --     (boolAlgebraVar @(D1 VGraphE) (\0 -> False))
  --     (unRecM $ cataRec @(RecBool (D1 VGraphE) _ _) $ iorefg1_var')
  --   return ()

  -- -- Test mutual recursion of "Fix"

  -- 6 <- runCIO do
  --   True <- cata @(K (Succ Zero) RecBoolInt) @BoolIntE
  --     (boolAlgebra @(D2 IntBoolE BoolIntE)) $ do
  --       cata @(K (Succ (Succ Zero)) RecIntBool) @IntBoolE
  --         (intAlgebra @(D2 IntBoolE BoolIntE)) $ do
  --           (unRecM2 $ cataRec @(RecBool (D2 IntBoolE BoolIntE) _ _) (fix2 False False))
  --   return ()

  -- 6 <- runCIO do
  --   False <- cata @(K (Succ Zero) RecBoolInt) @BoolIntE
  --     (boolAlgebra @(D2 IntBoolE BoolIntE)) $ do
  --       cata @(K (Succ (Succ Zero)) RecIntBool) @IntBoolE
  --         (intAlgebra @(D2 IntBoolE BoolIntE)) $ do
  --           (unRecM2 $ cataRec @(RecBool (D2 IntBoolE BoolIntE) _ _) (fix2 True False))
  --   return ()

  -- 6 <- runCIO do
  --   False <- cata @(K (Succ Zero) RecBoolInt) @BoolIntE
  --     (boolAlgebra @(D2 IntBoolE BoolIntE)) $ do
  --       cata @(K (Succ (Succ Zero)) RecIntBool) @IntBoolE
  --         (intAlgebra @(D2 IntBoolE BoolIntE)) $ do
  --           (unRecM2 $ cataRec @(RecBool (D2 IntBoolE BoolIntE) _ _) (fix2 False True))
  --   return ()

  -- -- Test mutual recursion of IORefGraph

  -- iorefg2_00 <- iorefg2 False False
  -- 2 <- runCIO do
  --   True <- cata @(K (Succ Zero) (RecBoolInt' (Succ (Succ Zero)))) @BoolInt'E
  --     (boolAlgebra @(D2 IntBool'E BoolInt'E)) $ do
  --       cata @(K (Succ (Succ Zero)) (RecIntBool' (Succ Zero))) @IntBool'E
  --         (intAlgebra @(D2 IntBool'E BoolInt'E)) $ do
  --           (unRecM2 $ cataRec @(RecBool (D2 IntBool'E BoolInt'E) _ _) iorefg2_00)
  --   return ()

  -- iorefg2_10 <- iorefg2 True False
  -- 2 <- runCIO do
  --   False <- cata @(K (Succ Zero) (RecBoolInt' (Succ (Succ Zero)))) @BoolInt'E
  --     (boolAlgebra @(D2 IntBool'E BoolInt'E)) $ do
  --       cata @(K (Succ (Succ Zero)) (RecIntBool' (Succ Zero))) @IntBool'E
  --         (intAlgebra @(D2 IntBool'E BoolInt'E)) $ do
  --           (unRecM2 $ cataRec @(RecBool (D2 IntBool'E BoolInt'E) _ _) iorefg2_10)
  --   return ()

  -- iorefg2_01 <- iorefg2 False True
  -- 2 <- runCIO do
  --   False <- cata @(K (Succ Zero) (RecBoolInt' (Succ (Succ Zero)))) @BoolInt'E
  --     (boolAlgebra @(D2 IntBool'E BoolInt'E)) $ do
  --       cata @(K (Succ (Succ Zero)) (RecIntBool' (Succ Zero))) @IntBool'E
  --         (intAlgebra @(D2 IntBool'E BoolInt'E)) $ do
  --           (unRecM2 $ cataRec @(RecBool (D2 IntBool'E BoolInt'E) _ _) iorefg2_01)
  --   return ()

  -- -- Test two-way recursion (the mutual one is unsupported)
  -- 2 <- recur @(K Zero RecIO.SemigroupRecFix) @SemigroupE
  --   (boolShareCount @SemigroupE)
  --   $ RecIO.SemigroupA $ Compose do
  --     recur <- ask
  --     let RecIO.RefFix r = iorefg1_True
  --     let RecIO.SemigroupA (Compose bef) = recur (Sum 1) r
  --     bef

  -- -- Test recursion of composition of IORefGraph and Free
  -- -- TODO

  -- -- Cleanup
  -- -- TODO

  return ()

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
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE TupleSections #-}
{-# OPTIONS_GHC -fplugin InversionOfControl.TcPlugin #-}
-- {-# OPTIONS_GHC -ddump-tc-trace -ddump-to-file -ddump-file-prefix=/tmp/foo #-}

module Main where

import Data.Traversable
import Data.Semigroup
import GHC.TypeLits (Symbol)
import Control.Monad.Reader
import Data.IORef
import Data.Functor.Compose
import Data.Fix hiding (cata)
import Control.Monad.Free
import qualified InversionOfControl.Recursion.IORefGraph as RecDag
import qualified InversionOfControl.Recursion.IORefGraphFree as RecDagFree
import qualified InversionOfControl.Recursion.Free as RecFree
import qualified InversionOfControl.Recursion.Fix as RecFix
import qualified InversionOfControl.Recursion.Pure as RecPure
import qualified InversionOfControl.Recursion as R
import InversionOfControl.Lift
import InversionOfControl.LiftN
import InversionOfControl.TypeDict
import InversionOfControl.KFn
import InversionOfControl.GMonadTrans
import Data.Kind
import Data.Functor.Classes
import Control.Monad
import Data.Foldable

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

term x = Right (Free (Compose x))
shared x = Right (Pure x)

iorefg1_val :: Bool -> IO (RecDag.RefFix (BoolFormula Int))
iorefg1_val val = do
  leq <- Pure <$> RecDag.buildFoldable (Leq 1 2)
  RecDag.buildFree $ Free $ And
    do Free $ Not $ Free $ And leq $ Free $ BoolLit val
    do Free $ And leq $ Free $ Not $ Free $ BoolLit val

iorefgf1_val :: Bool -> IO (RecDagFree.Ref (BoolFormula Int))
iorefgf1_val val = do
  leq <- Pure <$> RecDag.buildTopo 0 (RecDagFree.Ref $ Free $ Leq 1 2)
  return $ RecDagFree.Ref $ Free $ And
    do Free $ Not $ Free $ And leq $ Free $ BoolLit val
    do Free $ And leq $ Free $ Not $ Free $ BoolLit val

iorefg1_var :: IO (RecDag.RefFix (Compose (BoolFormula Int) (Either Word)))
iorefg1_var = do
  leq <- RecDag.buildFoldable $ Compose $ Leq 1 2
  RecDag.buildFree $ Free $ Compose $ And
    do term $ Not $ term $ And (shared leq) (Left 0)
    do term $ And (shared leq) (term $ Not $ Left 0)

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

type RunCIO d m a = E [k|runCIO|] (CIO a -> m a)
type GoBool d m = E [k|recBool|] (() -> [f|bool|] -> m Bool)
type GoInt d m = E [k|recInt|] (() -> [f|int|] -> m Int)

type RecAppBase d m =
  ( Monad m
  , forall a. KFn (RunCIO d m a)
  , Show [f|bool|]
  , Show [f|int|]
  ) :: Constraint

type RecAppAlg d m =
  ( RecAppBase d m
  , KFn (GoBool d m)
  , KFn (GoInt d m)
  ) :: Constraint

intAlgebra :: forall d m. RecAppAlg d m => IntFormula [f|bool|] [f|int|] -> m Int
intAlgebra = \case
  Count xs -> do
    kfn @(RunCIO d _ _) incCounter
    args <- mapM (R.cata @(GoBool d m)) xs
    let result = sum $ map fromEnum args
    kfn @(RunCIO d _ _) $ lift do print ("[]", result, args, xs)
    return result
  Plus x y -> do
    args <- (,) <$> R.cata @(GoInt d m) x <*> R.cata @(GoInt d m) y
    let result = uncurry (+) args
    kfn @(RunCIO d _ _) $ lift do print ("++", result, args, x, y)
    return result
  IntLit i -> do
    kfn @(RunCIO d _ _) $ lift do print ("II", i)
    return i

boolAlgebra :: forall d m. RecAppAlg d m => BoolFormula [f|int|] [f|bool|] -> m Bool
boolAlgebra = \case
  And x y -> do
    args <- (,) <$> R.cata @(GoBool d m) x <*> R.cata @(GoBool d m) y
    let result = uncurry (&&) args
    kfn @(RunCIO d _ _) $ lift do print ("&&", result, args, x, y)
    return result
  Not x -> do
    args <- R.cata @(GoBool d m) x
    let result = not args
    kfn @(RunCIO d _ _) $ lift do print ("!!", result, args, x)
    return result
  Leq x y -> do
    kfn @(RunCIO d _ _) incCounter
    args <- (,) <$> R.cata @(GoInt d m) x <*> R.cata @(GoInt d m) y
    let result = uncurry (<=) args
    kfn @(RunCIO d _ _) $ lift do print ("<=", result, args, x, y)
    return result
  BoolLit b -> do
    kfn @(RunCIO d _ _) $ lift do print ("BB", b)
    return b

boolAlgebraSimple :: forall d m.
  (Monad m, KFn (GoBool d m)) =>
  BoolFormula Int [f|bool|] -> m Bool
boolAlgebraSimple = \case
  BoolLit b -> pure b
  Leq x y -> pure do x <= y
  And x y -> (&&) <$> kfn @(GoBool d m) () x <*> kfn @(GoBool d m) () y
  Not x -> not <$> kfn @(GoBool d m) () x

data DSimple
type instance Definition DSimple =
  Name "lift" ()
  :+: Name "recBool" RecFix.Rec
  :+: Name "bool" (Fix (BoolFormula Int))
  :+: End

-- Valuated var recursion

type VarT = ReaderT (Word -> Bool)

data VarRec k
type instance R.Algebra
  (R.E (K nb (VarRec k)) p (Either Word r) (f (Either Word r)) mb xb) m0
 = p -> Either Word r -> f (Either Word r) -> mb xb
type instance R.MonadT
  (R.E (K nb (VarRec k)) p (Either Word r) (f (Either Word r)) mb xb) m0
 = R.MonadT (R.E k p r (Compose f (Either Word) r) mb xb) m0
instance
  ( R.Algebra (R.E k p r (Compose f (Either Word) r) mb xb) m0 ~
      (p -> r -> Compose f (Either Word) r -> mb xb)
  , R.Recursion (R.E k p r (Compose f (Either Word) r) mb xb) m0
  ) => R.Recursion (R.E (K nb (VarRec k)) p (Either Word r) (f (Either Word r)) mb xb) m0
 where
  runRecursion act algebra = R.runRecursion
    @(R.E k p r (Compose f (Either Word) r) mb xb)
    act
    \p r (Compose fr) -> algebra p (Right r) fr

instance
  ( KFn (E k (p -> r -> mb Bool))
  , LiftN nb (VarT m) mb
  , Monad m
  , Functor mb
  ) => KFn (E (K nb (VarRec k)) (p -> Either Word r -> mb Bool))
 where
  kfn p = \case
    Left w -> ($ w) <$> liftn @nb ask
    Right r -> kfn @(E k (p -> r -> mb Bool)) p r

-- Basic variants of settings

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
  Name "lift" ()
  :+: Name "recBool" RecFix.Rec
  :+: Name "bool" (Fix (BoolFormula Int))
  :+: Name "lift" ()
  :+: Follow D0

data FreeD
type instance Definition FreeD =
  Name "lift" ()
  :+: Name "recBool" RecFree.RecPure
  :+: Name "bool" (Free (BoolFormula Int) Bool)
  :+: Name "lift" ()
  :+: Follow D0

data DagD
type instance Definition DagD =
  Name "lift" ()
  :+: Name "recBool" (RecDag.RecFix (Succ Zero))
  :+: Name "bool" (RecDag.RefFix (BoolFormula Int))
  :+: Name "lift" ()
  :+: Follow D0

data DagFreeD
type instance Definition DagFreeD =
  Name "lift" ()
  :+: Name "recBool" (RecDagFree.Rec (Succ Zero))
  :+: Name "lift" ()
  :+: Name "lift" ()
  :+: Name "lift" ()
  :+: Name "bool" (RecDagFree.Ref (BoolFormula Int))
  :+: Follow D0

-- Variable valuation variants of settings

data VarFixD
type instance Definition VarFixD =
  Name "lift" ()
  :+: Name "recBool0" RecFix.Rec
  :+: Name "lift" ()
  :+: Name "recBool" (VarRec [ks|recBool0|])
  :+: Name "lift" ()
  :+: Name "bool" (Either Word (Fix (Compose (BoolFormula Int) (Either Word))))
  :+: Follow D0

data VarDagD
type instance Definition VarDagD =
  Name "lift" ()
  :+: Name "recBool0" (RecDag.RecFix (Succ (Succ Zero)))
  :+: Name "lift" ()
  :+: Name "recBool" (VarRec [ks|recBool0|])
  :+: Name "lift" ()
  :+: Name "bool" (Either Word (RecDag.RefFix (Compose (BoolFormula Int) (Either Word))))
  :+: Follow D0

-- Mutual recursion

type BoolIntFormulaBody = (BoolFormula IntBoolFormula BoolIntFormula)
type IntBoolFormulaBody = (IntFormula BoolIntFormula IntBoolFormula)
newtype BoolIntFormula = BoolIntFormula BoolIntFormulaBody
  deriving newtype Show
newtype IntBoolFormula = IntBoolFormula IntBoolFormulaBody
  deriving newtype Show

type BoolIntFormula'Body = (BoolFormula (RecDag.Ref IntBoolFormula') (RecDag.Ref BoolIntFormula'))
type IntBoolFormula'Body = (IntFormula (RecDag.Ref BoolIntFormula') (RecDag.Ref IntBoolFormula'))
newtype BoolIntFormula' = BoolIntFormula' BoolIntFormula'Body
newtype IntBoolFormula' = IntBoolFormula' IntBoolFormula'Body
type BoolIntFormula'Ref = RecDag.Ref BoolIntFormula'
type IntBoolFormula'Ref = RecDag.Ref IntBoolFormula'

fix2 :: Bool -> Bool -> BoolIntFormula
fix2 val1 val2 = BoolIntFormula $ And
  (BoolIntFormula $ Not $ BoolIntFormula $ And leq (BoolIntFormula $ BoolLit val1))
  (BoolIntFormula $ And leq (BoolIntFormula $ Not $ BoolIntFormula $ BoolLit val1))
  where
    leq = BoolIntFormula $ Leq count2 (IntBoolFormula $ IntLit 2)
    count = IntBoolFormula $ Count [tv2, BoolIntFormula $ BoolLit True, tv2]
    count2 = IntBoolFormula $ Plus count count
    tv2 = BoolIntFormula $ And (BoolIntFormula $ BoolLit True) (BoolIntFormula $ BoolLit val2)

iorefg2 :: Bool -> Bool -> IO (RecDag.Ref BoolIntFormula')
iorefg2 val1 val2 = do
  v2 <- RecDag.buildTopo 0 $ BoolIntFormula' $ BoolLit val2
  print ("v2", v2)
  t <- RecDag.buildTopo 0 $ BoolIntFormula' $ BoolLit True
  print ("t", t)
  tv2 <- RecDag.buildTopo 1 $ BoolIntFormula' $ And t v2
  print ("tv2", tv2)
  count <- RecDag.buildTopo 2 $ IntBoolFormula' $ Count [tv2, t, tv2]
  print ("count", count)
  plus <- RecDag.buildTopo 3 $ IntBoolFormula' $ Plus count count
  print ("plus", plus)
  l1 <- RecDag.buildTopo 0 $ IntBoolFormula' $ IntLit 2
  print ("l1", l1)
  leq <- RecDag.buildTopo 3 $ BoolIntFormula' $ Leq plus l1
  print ("leq", leq)
  v1 <- RecDag.buildTopo 0 $ BoolIntFormula' $ BoolLit val1
  print ("v1", v1)
  nv1 <- RecDag.buildTopo 1 $ BoolIntFormula' $ Not v1
  print ("nv1", nv1)
  leqv1 <- RecDag.buildTopo 4 $ BoolIntFormula' $ And leq v1
  print ("leqv1", leqv1)
  leqnv1 <- RecDag.buildTopo 4 $ BoolIntFormula' $ And leq nv1
  print ("leqnv1", leqnv1)
  nleqv1 <- RecDag.buildTopo 5 $ BoolIntFormula' $ Not leqv1
  print ("nleqv1", nleqv1)
  RecDag.buildTopo 6 $ BoolIntFormula' $ And nleqv1 leqnv1

data RecIntBool
type instance R.Algebra (R.E (K nb RecIntBool) p IntBoolFormula IntBoolFormulaBody mb xb) m0 =
  p -> IntBoolFormula -> IntBoolFormulaBody -> mb xb
type instance R.MonadT (R.E (K nb RecIntBool) p IntBoolFormula IntBoolFormulaBody mb xb) m0 =
  RecFix.RecT p IntBoolFormula mb xb m0
instance
  (r ~ IntBoolFormula, a ~ IntBoolFormulaBody)
  => R.Recursion (R.E (K nb RecIntBool) p r a mb xb) m0
 where
  runRecursion act algebra = RecFix.runRecursion act (\p r@(IntBoolFormula a) -> algebra p r a)
instance
  RecFix.RecurC nb mb xb p IntBoolFormula
  => KFn (R.RecE nb RecIntBool p IntBoolFormula mb xb)
 where
  kfn = RecFix.recur @nb

data RecBoolInt
type instance R.Algebra (R.E (K nb RecBoolInt) p BoolIntFormula BoolIntFormulaBody mb xb) m0 =
  p -> BoolIntFormula -> BoolIntFormulaBody -> mb xb
type instance R.MonadT (R.E (K nb RecBoolInt) p BoolIntFormula BoolIntFormulaBody mb xb) m0 =
  RecFix.RecT p BoolIntFormula mb xb m0
instance
  (r ~ BoolIntFormula, a ~ BoolIntFormulaBody)
  => R.Recursion (R.E (K nb RecBoolInt) p r a mb xb) m0
 where
  runRecursion act algebra = RecFix.runRecursion act (\p r@(BoolIntFormula a) -> algebra p r a)
instance
  RecFix.RecurC nb mb xb p BoolIntFormula
  => KFn (R.RecE nb RecBoolInt p BoolIntFormula mb xb)
 where
  kfn = RecFix.recur @nb

type RecIntBool'T p = RecDag.RecT p IntBoolFormula'
data (RecIntBool' n0)
type instance R.Algebra
  (R.E (K nb (RecIntBool' n0)) p IntBoolFormula'Ref IntBoolFormula'Body mb xb) m0
  = p -> IntBoolFormula'Ref -> IntBoolFormula'Body -> mb xb
type instance R.MonadT
  (R.E (K nb (RecIntBool' n0)) p IntBoolFormula'Ref IntBoolFormula'Body mb xb) m0
  = RecIntBool'T p mb xb m0
instance
  (r ~ IntBoolFormula'Ref, a ~ IntBoolFormula'Body, RecDag.RunRecursionC m0 n0)
  => R.Recursion (R.E (K nb (RecIntBool' n0)) p r a mb xb) m0
 where
  runRecursion act algebra =
    RecDag.runRecursion @n0 act (\p r (IntBoolFormula' a) -> algebra p r a)
instance
  RecDag.RecurC n0 nb mb xb p IntBoolFormula'
  => KFn (R.RecE nb (RecIntBool' n0) p IntBoolFormula'Ref mb xb)
 where
  kfn = RecDag.recur @n0 @nb

type RecBoolInt'T p = RecDag.RecT p BoolIntFormula'
data (RecBoolInt' n0)
type instance R.Algebra
  (R.E (K nb (RecBoolInt' n0)) p BoolIntFormula'Ref BoolIntFormula'Body mb xb) m0
  = p -> BoolIntFormula'Ref -> BoolIntFormula'Body -> mb xb
type instance R.MonadT
  (R.E (K nb (RecBoolInt' n0)) p BoolIntFormula'Ref BoolIntFormula'Body mb xb) m0
  = RecBoolInt'T p mb xb m0
instance
  (r ~ BoolIntFormula'Ref, a ~ BoolIntFormula'Body, RecDag.RunRecursionC m0 n0)
  => R.Recursion (R.E (K nb (RecBoolInt' n0)) p r a mb xb) m0
 where
  runRecursion act algebra =
    RecDag.runRecursion @n0 act (\p r (BoolIntFormula' a) -> algebra p r a)
instance
  RecDag.RecurC n0 nb mb xb p BoolIntFormula'
  => KFn (R.RecE nb (RecBoolInt' n0) p BoolIntFormula'Ref mb xb)
 where
  kfn = RecDag.recur @n0 @nb

data BoolIntD
type instance Definition BoolIntD =
  Name "lift" ()
  :+: Name "recBool" RecBoolInt
  :+: Name "lift" ()
  :+: Name "recInt" RecIntBool
  :+: Name "lift" ()
  :+: Name "bool" BoolIntFormula
  :+: Name "int" IntBoolFormula
  :+: Follow D0

data BoolIntD'
type instance Definition BoolIntD' =
  Name "lift" ()
  :+: Name "recBool" (RecBoolInt' (Succ (Succ Zero)))
  :+: Name "lift" ()
  :+: Name "recInt" (RecIntBool' (Succ Zero))
  :+: Name "lift" ()
  :+: Name "bool" BoolIntFormula'Ref
  :+: Name "int" IntBoolFormula'Ref
  :+: Follow D0

type TestSingleCata d t =
  R.E1 [k|recBool|] () [f|bool|] (BoolFormula [f|int|] [f|bool|]) t Bool CIO

testSingle :: forall d t.
  ( RecAppAlg d (R.RecurMonad1 t Bool CIO)
  , R.BasicRecursion1C (TestSingleCata d t) CIO
  ) => String -> Bool -> Int -> [f|bool|] -> IO ()
testSingle tag wantedResult wantedCount r = do
  count <- runCIO do
    result <- R.runRecursion @(TestSingleCata d t)
      do R.unRecurMonad1 do R.cata @(GoBool d _) r
      do \_ _ -> boolAlgebra @d
    when (wantedResult /= result) do
      error do "testSingle result " ++ tag ++ " " ++ show wantedResult ++ " != " ++ show result
  when (wantedCount /= count) do
    error do "testSingle count " ++ tag ++ " " ++ show wantedCount ++ " != " ++ show count

type TestMutualCata2 d t2 t1 =
  R.E2_2 [k|recBool|] () [f|bool|] (BoolFormula [f|int|] [f|bool|]) t2 Bool t1 Int CIO
type TestMutualCata1 d t2 t1 =
  R.E2_1 [k|recInt|] () [f|int|] (IntFormula [f|bool|] [f|int|]) t2 Bool t1 Int CIO

testMutual :: forall d t2 t1.
  ( RecAppAlg d (R.RecurMonad2 t2 Bool t1 Int CIO)
  , R.BasicRecursion2C (TestMutualCata2 d t2 t1) (TestMutualCata1 d t2 t1) CIO
  ) => String -> Bool -> Int -> [f|bool|] -> IO ()
testMutual tag wantedResult wantedCount r = do
  count <- runCIO do
    result <-
      R.runRecursion @(TestMutualCata1 d t2 t1)
        do R.runRecursion @(TestMutualCata2 d t2 t1)
            do R.unRecurMonad2 do R.cata @(GoBool d _) r
            do \_ _ -> boolAlgebra @d
        do \_ _ -> intAlgebra @d
    when (wantedResult /= result) do
      error do "testSingle result " ++ tag ++ " " ++ show wantedResult ++ " != " ++ show result
  when (wantedCount /= count) do
    error do "testSingle count " ++ tag ++ " " ++ show wantedCount ++ " != " ++ show count

type TestSingleVarCata d t =
  R.E1 [k|recBool|] () [f|bool|] (BoolFormula [f|int|] [f|bool|]) t Bool (VarT CIO)

testSingleVar :: forall d t.
  ( RecAppAlg d (R.RecurMonad1 t Bool (VarT CIO))
  , R.BasicRecursion1C (TestSingleVarCata d t) (VarT CIO)
  ) => String -> Bool -> Int -> (Word -> Bool) -> [f|bool|] -> IO ()
testSingleVar tag wantedResult wantedCount valuation r = do
  count <- runCIO do
    runReaderT
      do
        result <- R.runRecursion @(TestSingleVarCata d t)
          do R.unRecurMonad1 do R.cata @(GoBool d _) r
          do \_ _ -> boolAlgebra @d
        when (wantedResult /= result) do
          error do "testSingle result " ++ tag ++ " " ++ show wantedResult ++ " != " ++ show result
      valuation
  when (wantedCount /= count) do
    error do "testSingle count " ++ tag ++ " " ++ show wantedCount ++ " != " ++ show count

main ∷ IO ()
main = do
  -- Simple test

  True <- RecFix.runRecursion
    do R.unRecurMonad1 do RecFix.recur @(Succ Zero) () (fix1_val False)
    do \_ (Fix a) -> boolAlgebraSimple @DSimple a

  True <- R.runRecursion @(R.E (K (Succ Zero) RecFix.Rec) _ _ _ _ _)
    do R.unRecurMonad1 do kfn @(GoBool DSimple _) () (fix1_val False)
    do \_ _ -> boolAlgebraSimple @DSimple

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

  testSingle @FixD "fix1_true" False 2 (fix1_val True)
  testSingle @FixD "fix1_false" True 2 (fix1_val False)

  testSingleVar @VarFixD "fix1_var_true" False 2 (\0 -> True) (Right fix1_var)
  testSingleVar @VarFixD "fix1_var_false" True 2 (\0 -> False) (Right fix1_var)

  -- Test recursion of Free

  testSingle @FreeD "free1_true" False 2 do fmap (\0 -> True) free1
  testSingle @FreeD "free1_false" True 2 do fmap (\0 -> False) free1

  -- Test recursion of IORefGraph

  iorefg1_True <- iorefg1_val True
  testSingle @DagD "iorefg1_True" False 1 iorefg1_True
  iorefg1_False <- iorefg1_val False
  testSingle @DagD "iorefg1_False" True 1 iorefg1_False

  iorefg1_var' <- iorefg1_var
  testSingleVar @VarDagD "iorefg1_var_true" False 1 (\0 -> True) (Right iorefg1_var')
  testSingleVar @VarDagD "iorefg1_var_false" True 1 (\0 -> False) (Right iorefg1_var')

  -- Test mutual recursion of "Fix"

  testMutual @BoolIntD "fix2_False_False" True 6 do fix2 False False
  testMutual @BoolIntD "fix2_True_False" False 6 do fix2 True False
  testMutual @BoolIntD "fix2_False_True" False 6 do fix2 False True

  -- Test mutual recursion of IORefGraph

  iorefg2_00 <- iorefg2 False False
  testMutual @BoolIntD' "iorefg2_False_False" True 2 iorefg2_00
  iorefg2_10 <- iorefg2 True False
  testMutual @BoolIntD' "iorefg2_True_False" False 2 iorefg2_10

  -- Test two-way recursion (the mutual one is unsupported). An example for DAG and Fix is given
  -- but it is not yet unified via classes.

  2 <- RecDag.runMergingRecursion_Fix @Zero
    do R.unRecurMonad1 do
        r <- RecDag.descend_Fix @Zero @(Succ Zero) (Sum 1) iorefg1_True
        RecDag.finishDescend @Zero @(Succ Zero)
        RecDag.ascend_Fix @Zero @(Succ Zero) r
    do \(Sum p) _ fr -> do
        (p,) <$> for fr \child -> RecDag.descend_Fix @Zero @(Succ Zero) (Sum 1) child
    do \(p, fr) -> do
        (sum -> childN) <- for fr do RecDag.ascend_Fix @Zero @(Succ Zero)
        return if p > 1 then childN + 1 else childN

  2 <- RecFix.runMergingRecursion_Fix
    do R.unRecurMonad1 do
        r <- RecFix.descend_Fix @(Succ Zero) (Sum 1) (fix1_val True)
        RecFix.finishDescend
        RecFix.ascend_Fix r
    do \(Sum p) _ fr -> do
        (p,) <$> for fr \child -> RecFix.descend_Fix @(Succ Zero) (Sum 1) child
    do \(p, fr) -> do
        (sum -> childN) <- for fr do RecFix.ascend_Fix
        return if p > 1 then childN + 1 else childN

  -- Test composition of IORefGraph and Free

  iorefgf1_True <- iorefgf1_val True
  testSingle @DagFreeD "iorefgf1_True" False 1 iorefgf1_True
  iorefgf1_False <- iorefgf1_val False
  testSingle @DagFreeD "iorefgf1_False" True 1 iorefgf1_False

  return ()

{-# LANGUAGE UnicodeSyntax #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE LambdaCase #-}

module Main where

import Control.Monad.Reader
import Data.IORef
import Data.Functor.Compose
import Data.Fix hiding (cata)
import Control.Monad.Free
import qualified InversionOfControl.Recursion.IORefGraph as RecIO
import qualified InversionOfControl.Recursion.Free as RecFree
import qualified InversionOfControl.Recursion.Fix as RecFix
import InversionOfControl.Recursion
import InversionOfControl.Lift

data BoolFormula int bool =
  And bool bool
  | Not bool
  | Leq int int
  | BoolLit Bool
  deriving (Show, Eq, Functor, Foldable, Traversable)

data IntFormula bool int =
  Count [bool]
  | Plus int int
  | IntLit Int
  deriving (Show, Eq, Functor, Foldable, Traversable)

fix1_val :: Bool -> Fix (BoolFormula Int)
fix1_val val = Fix $ And
  (Fix $ Not $ Fix $ And (Fix $ Leq 1 2) (Fix $ BoolLit val))
  (Fix $ And (Fix $ Leq 1 2) (Fix $ Not $ Fix $ BoolLit val))

fterm x = Right (Fix (Compose x))

fix1_var :: Fix (Compose (BoolFormula Int) (Either Word))
fix1_var = Fix $ Compose $ And
  (fterm $ Not $ fterm $ And (fterm $ Leq 1 2) (Left 0))
  (fterm $ And (fterm $ Leq 1 2) (fterm $ Not $ Left 0))

-- Free is just the same as Fix+Compose+Either (even in memory, as Fix and Compose are newtypes)
free1 :: Free (BoolFormula Int) Word
free1 = Free $ And
  (Free $ Not $ Free $ And (Free $ Leq 1 2) (Pure 0))
  (Free $ And (Free $ Leq 1 2) (Free $ Not $ Pure 0))

term x = Right (Free (Compose x))
shared x = Right (Pure x)

iorefg1_val :: Bool -> IO (RecIO.RefFix (BoolFormula Int))
iorefg1_val val = do
  leq <- RecIO.buildFoldable $ Leq 1 2
  RecIO.buildFree $ Free $ And
    (Free $ Not $ Free $ And (Pure leq) (Free $ BoolLit val))
    (Free $ And (Pure leq) (Free $ Not $ Free $ BoolLit val))

iorefg1_var :: IO (RecIO.RefFix (Compose (BoolFormula Int) (Either Word)))
iorefg1_var = do
  leq <- RecIO.buildFoldable $ Compose $ Leq 1 2
  RecIO.buildFree $ Free $ Compose $ And
    (term $ Not $ term $ And (shared leq) (Left 0))
    (term $ And (shared leq) (term $ Not $ Left 0))

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

boolAlgebra :: (int -> CIO Int) -> (bool -> CIO Bool) -> BoolFormula int bool -> CIO Bool
boolAlgebra _ getBool (And x y) = (&&) <$> getBool x <*> getBool y
boolAlgebra _ getBool (Not x) = not <$> getBool x
boolAlgebra getInt _ (Leq x y) = incCounter >> (<=) <$> getInt x <*> getInt y
boolAlgebra _ _ (BoolLit b) = return b

boolAlgebraVar
  :: (Word -> Bool)
  -> (int -> CIO Int)
  -> (bool -> CIO Bool)
  -> Compose (BoolFormula int) (Either Word) bool
  -> CIO Bool
boolAlgebraVar valuation getInt getBool (Compose fr) = boolAlgebra getInt getBool' fr
  where
    getBool' = \case
      Left x -> return $ valuation x
      Right x -> getBool x

type GenFixE f = E
  (K (Succ Zero) RecFix.Rec)
  ()
  (Fix f)
  (f (Fix f))
  (CIO Bool)
  CIO
  CIO
type FixE = GenFixE (BoolFormula Int)
type VFixE = GenFixE (Compose (BoolFormula Int) (Either Word))

type GenGraphE f = E
  (K (Succ Zero) (RecIO.Rec Zero))
  ()
  (RecIO.RefFix f)
  (f (RecIO.RefFix f))
  (CIO Bool)
  CIO
  CIO
type GraphE = GenGraphE (BoolFormula Int)
type VGraphE = GenGraphE (Compose (BoolFormula Int) (Either Word))

type FreeE = E
  (K (Succ Zero) RecFree.Rec)
  ()
  (Free (BoolFormula Int) (CIO Bool))
  (BoolFormula Int (Free (BoolFormula Int) (CIO Bool)))
  (CIO Bool)
  CIO
  CIO

main ∷ IO ()
main = do
  1 <- runCIO do
    False <- boolAlgebra pure pure $ And True False
    True <- boolAlgebra pure pure $ Not False
    True <- boolAlgebra pure pure $ Leq 1 2
    False <- boolAlgebra pure pure $ BoolLit False
    return ()

  2 <- runCIO do
    False <- cata @FixE (boolAlgebra pure) ($ fix1_val True)
    return ()

  2 <- runCIO do
    True <- cata @FixE (boolAlgebra pure) ($ fix1_val False)
    return ()

  2 <- runCIO do
    False <- cata @VFixE (boolAlgebraVar (\0 -> True) pure) ($ fix1_var)
    return ()

  2 <- runCIO do
    True <- cata @VFixE (boolAlgebraVar (\0 -> False) pure) ($ fix1_var)
    return ()

  2 <- runCIO do
    False <- cata @FreeE (boolAlgebra pure) ($ fmap (\0 -> pure True) free1)
    return ()

  2 <- runCIO do
    True <- cata @FreeE (boolAlgebra pure) ($ fmap (\0 -> pure False) free1)
    return ()

  iorefg1_True <- iorefg1_val True
  iorefg1_False <- iorefg1_val False
  iorefg1_var' <- iorefg1_var

  1 <- runCIO do
    False <- cata @GraphE (boolAlgebra pure) ($ iorefg1_True)
    return ()

  1 <- runCIO do
    True <- cata @GraphE (boolAlgebra pure) ($ iorefg1_False)
    return ()

  1 <- runCIO do
    True <- cata @VGraphE (boolAlgebraVar (\0 -> False) pure) ($ iorefg1_var')
    return ()

  1 <- runCIO do
    False <- cata @VGraphE (boolAlgebraVar (\0 -> True) pure) ($ iorefg1_var')
    return ()

  return ()

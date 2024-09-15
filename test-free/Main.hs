{-# LANGUAGE CPP #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE UnicodeSyntax #-}
{-# OPTIONS_GHC -fplugin InversionOfControl.TcPlugin #-}

module Main where

import Data.IORef
import Data.Time.Clock.POSIX (getPOSIXTime)
import qualified DictImpl as D
import qualified FreeImpl as F
import qualified MonadImpl as M

main ∷ IO ()
main = do
  putStrLn "FreeImpl"
  F.runApp $ do
    F.printRandomFactorialFibonacci
    F.safeScenario
    F.safeScenario
    F.safeScenario
    F.safeScenario
    F.safeScenario

  putStrLn "MonadImpl"
  M.printRandomFactorialFibonacci
  M.safeScenario
  M.safeScenario
  M.safeScenario
  M.safeScenario
  M.safeScenario

  putStrLn "DictImpl"
  D.printRandomFactorialFibonacci @D.AppD
  D.safeScenario @D.AppD
  D.safeScenario @D.AppD
  D.safeScenario @D.AppD
  D.safeScenario @D.AppD
  D.safeScenario @D.AppD

  putStrLn "FreeImpl"
  mocks ← F.RandomValueMocks <$> newIORef [4, 6, 85, 23, 50]
  F.runApp' mocks $ do
    F.printRandomFactorialFibonacci
    F.safeScenario
    F.safeScenario
    F.safeScenario

  putStrLn "MonadImpl"
  mocks ← M.RandomValueMocks <$> newIORef [4, 6, 85, 23, 50]
  M.runMockApp mocks $ do
    M.printRandomFactorialFibonacci
    M.safeScenario
    M.safeScenario
    M.safeScenario

  putStrLn "DictImpl"
  mocks ← D.RandomValueMocks <$> newIORef [4, 6, 85, 23, 50]
  D.runMockApp mocks $ do
    D.printRandomFactorialFibonacci @D.MockAppD
    D.safeScenario @D.MockAppD
    D.safeScenario @D.MockAppD
    D.safeScenario @D.MockAppD

  let stopTime = 0.7

  putStrLn "FreeImpl"
  let bench n = do
        tic ← getPOSIXTime
        F.benchmark n
        toc ← getPOSIXTime
        print (n, toc - tic)
        if toc - tic < stopTime
          then bench (n * 10)
          else return ()
  bench 1000

  putStrLn "MonadImpl"
  let bench n = do
        tic ← getPOSIXTime
        M.benchmark n
        toc ← getPOSIXTime
        print (n, toc - tic)
        if toc - tic < stopTime
          then bench (n * 10)
          else return ()
  bench 1000

  putStrLn "DictImpl"
  let bench n = do
        tic ← getPOSIXTime
        D.benchmark n
        toc ← getPOSIXTime
        print (n, toc - tic)
        if toc - tic < stopTime
          then bench (n * 10)
          else return ()
  bench 1000

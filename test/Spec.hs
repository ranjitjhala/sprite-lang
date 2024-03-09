{-# LANGUAGE OverloadedStrings    #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Main where

import qualified Control.Concurrent.STM as STM
import qualified Data.Functor.Compose   as Functor
import qualified Data.IntMap            as IntMap
-- import qualified Data.Map               as Map
import qualified Control.Monad.State    as State
import Control.Monad.Trans.Class (lift)

import Data.Char
import Data.Maybe (fromMaybe)
import Data.Monoid (Sum(..), (<>))
import Control.Applicative
import System.Directory
import System.Exit
import System.FilePath
-- import System.Environment
import System.IO
import System.IO.Error
import System.Process
import Text.Printf

import Test.Tasty
import Test.Tasty.HUnit
import Test.Tasty.Ingredients.Rerun
-- import Test.Tasty.Options
import Test.Tasty.Runners
import Test.Tasty.Runners.AntXML
import Paths_sprite

main :: IO ()
main = defaultMainWithIngredients [testRunner] =<< allTests

allTests = group "Tests"
  [ l1Tests
  , l2Tests
  , l3Tests
  , l4Tests
  , l5Tests
  , l6Tests
  , l8Tests
  ]

l1Tests :: IO TestTree
l1Tests = group "L1" $ langTests "L1" 1

l2Tests :: IO TestTree
l2Tests = group "L2" $ langTests "L1" 2
                    ++ langTests "L2" 2

l3Tests :: IO TestTree
l3Tests = group "L3" $ langTests "L1" 3
                    ++ langTests "L2" 3
                    ++ langTests "L3" 3

l4Tests :: IO TestTree
l4Tests = group "L4" $ langTests "L1" 4
                    ++ langTests "L2" 4
                    ++ langTests "L3" 4
                    ++ langTests "L4" 4

l5Tests :: IO TestTree
l5Tests = group "L5" $ langTests "L1" 5
                    ++ langTests "L2" 5
                    ++ langTests "L3" 5
                    ++ langTests "L4" 5
                    ++ langTests "L5" 5

l6Tests :: IO TestTree
l6Tests = group "L6" $ langTests "L1" 6
                    ++ langTests "L2" 6
                    ++ langTests "L3" 6
                    ++ langTests "L4" 6
                    ++ langTests "L5" 6
                    ++ langTests "L6" 6

l8Tests :: IO TestTree
l8Tests = group "L8" $ langTests "L7" 8
                    ++ langTests "L8" 8


langTests :: String -> Int -> [IO TestTree]
langTests lang n =
  [ testGroup (name "pos") <$> dirTests (spriteCmd n) (dir "pos") []  ExitSuccess
  , testGroup (name "neg") <$> dirTests (spriteCmd n) (dir "neg") []  (ExitFailure 1)
  ]
  where
    name :: String -> String
    name k = printf "%s-%s-%d" k lang n
    dir  k = "test" </> lang </> k

testRunner :: Ingredient
testRunner = rerunningTests
               [ listingTests
               , combineReporters myConsoleReporter antXMLRunner
               , myConsoleReporter
               ]

myConsoleReporter :: Ingredient
myConsoleReporter = combineReporters consoleTestReporter loggingTestReporter

-- | Combine two @TestReporter@s into one.
--
-- Runs the reporters in sequence, so it's best to start with the one
-- that will produce incremental output, e.g. 'consoleTestReporter'.
combineReporters :: Ingredient -> Ingredient -> Ingredient
combineReporters (TestReporter opts1 run1) (TestReporter opts2 run2)
  = TestReporter (opts1 ++ opts2) $ \opts tree -> do
      f1 <- run1 opts tree
      f2 <- run2 opts tree
      return $ \smap -> f1 smap >> f2 smap
combineReporters _ _ = error "combineReporters needs TestReporters"


---------------------------------------------------------------------------
dirTests :: TestCmd -> FilePath -> [FilePath] -> ExitCode -> IO [TestTree]
---------------------------------------------------------------------------
dirTests testCmd root ignored code = do
  files    <- walkDirectory root
  let tests = [ rel | f <- files, isTest f, let rel = makeRelative root f, rel `notElem` ignored ]
  return    $ mkTest testCmd code root <$> tests

isTest   :: FilePath -> Bool
isTest f = takeExtension f `elem` [".re"]

---------------------------------------------------------------------------
mkTest :: TestCmd -> ExitCode -> FilePath -> FilePath -> TestTree
---------------------------------------------------------------------------
mkTest testCmd code dir file
  = testCase file $
      if test `elem` knownToFail
      then do
        printf "%s is known to fail: SKIPPING" test
        assertEqual "" True True
      else do
        createDirectoryIfMissing True $ takeDirectory log
        bin <- binPath execName
        withFile log WriteMode $ \h -> do
          let cmd     = testCmd bin dir file
          (_,_,_,ph) <- createProcess $ (shell cmd) {std_out = UseHandle h, std_err = UseHandle h}
          c          <- waitForProcess ph
          assertEqual ("Wrong exit code: " ++ cmd) code c
  where
    test = dir </> file
    log  = let (d,f) = splitFileName file in dir </> d </> ".liquid" </> f <.> "log"

binPath :: FilePath -> IO FilePath
binPath pkgName = (</> pkgName) <$> getBinDir

knownToFail = []

---------------------------------------------------------------------------
-- | Project specific configuration ---------------------------------------
---------------------------------------------------------------------------

type TestCmd = FilePath -> FilePath -> FilePath -> String

execName :: FilePath
execName = "sprite"

spriteCmd :: Int -> TestCmd
spriteCmd n bin dir file = printf "cd %s && %s %d %s" dir bin n file


----------------------------------------------------------------------------------------
-- Generic Helpers
----------------------------------------------------------------------------------------

group n xs = testGroup n <$> sequence xs

----------------------------------------------------------------------------------------
walkDirectory :: FilePath -> IO [FilePath]
----------------------------------------------------------------------------------------
walkDirectory root
  = do (ds,fs) <- partitionM doesDirectoryExist . candidates =<< (getDirectoryContents root `catchIOError` const (return []))
       (fs++) <$> concatMapM walkDirectory ds
  where
    candidates fs = [root </> f | f <- fs, not (isExtSeparator (head f))]

partitionM :: Monad m => (a -> m Bool) -> [a] -> m ([a],[a])
partitionM f = go [] []
  where
    go ls rs []     = return (ls,rs)
    go ls rs (x:xs) = do b <- f x
                         if b then go (x:ls) rs xs
                              else go ls (x:rs) xs

-- isDirectory :: FilePath -> IO Bool
-- isDirectory = fmap Posix.isDirectory . Posix.getFileStatus

concatMapM :: Applicative m => (a -> m [b]) -> [a] -> m [b]
concatMapM _ []     = pure []
concatMapM f (x:xs) = (++) <$> f x <*> concatMapM f xs

-- -- this is largely based on ocharles' test runner at
-- -- https://github.com/ocharles/tasty-ant-xml/blob/master/Test/Tasty/Runners/AntXML.hs#L65
-- loggingTestReporter :: Ingredient
-- loggingTestReporter = TestReporter [] $ \opts tree -> Just $ \smap -> do
--   let
--     runTest _ testName _ = Traversal $ Functor.Compose $ do
--         i <- State.get

--         summary <- lift $ STM.atomically $ do
--           status <- STM.readTVar $
--             fromMaybe (error "Attempted to lookup test by index outside bounds") $
--               IntMap.lookup i smap

--           let mkSuccess time = [(testName, time, True)]
--               mkFailure time = [(testName, time, False)]

--           case status of
--             -- If the test is done, generate a summary for it
--             Done result
--               | resultSuccessful result
--                   -> pure (mkSuccess (resultTime result))
--               | otherwise
--                   -> pure (mkFailure (resultTime result))
--             -- Otherwise the test has either not been started or is currently
--             -- executing
--             _ -> STM.retry

--         Const summary <$ State.modify (+ 1)

--     runGroup group children = Traversal $ Functor.Compose $ do
--       Const soFar <- Functor.getCompose $ getTraversal children
--       pure $ Const $ map (\(n,t,s) -> (group</>n,t,s)) soFar

--     computeFailures :: StatusMap -> IO Int
--     computeFailures = fmap getSum . getApp . foldMap (\var -> Ap $
--       (\r -> Sum $ if resultSuccessful r then 0 else 1) <$> getResultFromTVar var)

--     getResultFromTVar :: STM.TVar Status -> IO Result
--     getResultFromTVar var =
--       STM.atomically $ do
--         status <- STM.readTVar var
--         case status of
--           Done r -> return r
--           _ -> STM.retry

--   (Const summary, _tests) <-
--      flip State.runStateT 0 $ Functor.getCompose $ getTraversal $
--       foldTestTree
--         trivialFold { foldSingle = runTest, foldGroup = runGroup }
--         opts
--         tree

--   return $ \_elapsedTime -> do
--     -- get some semblance of a hostname
--     host <- takeWhile (/='.') . takeWhile (not . isSpace) <$> readProcess "hostname" [] []
--     -- don't use the `time` package, major api differences between ghc 708 and 710
--     time <- head . lines <$> readProcess "date" ["+%Y-%m-%dT%H-%M-%S"] []
--     -- build header
--     ref <- gitRef
--     timestamp <- gitTimestamp
--     epochTime <- gitEpochTimestamp
--     hash <- gitHash
--     let hdr = unlines [ref ++ " : " ++ hash,
--                        "Timestamp: " ++ timestamp,
--                        "Epoch Timestamp: " ++ epochTime,
--                        headerDelim,
--                        "test, time(s), result"]


--     let dir = "test" </> "logs" </> host ++ "-" ++ time
--     let smry = "test" </> "logs" </> "cur" </> "summary.csv"
--     writeFile smry $ unlines
--                    $ hdr
--                    : map (\(n, t, r) -> printf "%s, %0.4f, %s" n t (show r)) summary
--     -- system $ "cp -r tests/logs/cur " ++ dir
--     (==0) <$> computeFailures smap


-- this is largely based on ocharles' test runner at
-- https://github.com/ocharles/tasty-ant-xml/blob/master/Test/Tasty/Runners/AntXML.hs#L65
loggingTestReporter :: Ingredient
loggingTestReporter = TestReporter [] $ \opts tree -> Just $ \smap -> do
  let
    runTest _ testName _ = Traversal $ Functor.Compose $ do
        i <- State.get

        summary <- lift $ STM.atomically $ do
          status <- STM.readTVar $
            fromMaybe (error "Attempted to lookup test by index outside bounds") $
              IntMap.lookup i smap

          let mkSuccess time = [(testName, time, True)]
              mkFailure time = [(testName, time, False)]

          case status of
            -- If the test is done, generate a summary for it
            Done result
              | resultSuccessful result
                  -> pure (mkSuccess (resultTime result))
              | otherwise
                  -> pure (mkFailure (resultTime result))
            -- Otherwise the test has either not been started or is currently
            -- executing
            _ -> STM.retry

        Const summary <$ State.modify (+ 1)

    runGroup _ group' children = Traversal $ Functor.Compose $ do
      Const soFar <- Functor.getCompose $ getTraversal $ mconcat children
      pure $ Const $ map (\(n,t,s) -> (group' </> n,t,s)) soFar

    computeFailures :: StatusMap -> IO Int
    computeFailures = fmap getSum . getApp . foldMap (\var -> Ap $
      (\r -> Sum $ if resultSuccessful r then 0 else 1) <$> getResultFromTVar var)

    getResultFromTVar :: STM.TVar Status -> IO Result
    getResultFromTVar var =
      STM.atomically $ do
        status <- STM.readTVar var
        case status of
          Done r -> return r
          _ -> STM.retry

  (Const summary, _tests) <-
     flip State.runStateT 0 $ Functor.getCompose $ getTraversal $
      foldTestTree
        trivialFold { foldSingle = runTest, foldGroup = runGroup }
        opts
        tree

  return $ \_elapsedTime -> do
    -- don't use the `time` package, major api differences between ghc 708 and 710
    -- build header
    ref <- gitRef
    timestamp <- gitTimestamp
    epochTime <- gitEpochTimestamp
    hash <- gitHash
    let hdr = unlines [ref ++ " : " ++ hash,
                       "Timestamp: " ++ timestamp,
                       "Epoch Timestamp: " ++ epochTime,
                       headerDelim,
                       "test, time(s), result"]

    let smry = "test" </> "logs" </> "cur" </> "summary.csv"
    writeFile smry $ unlines
                   $ hdr
                   : map (\(n, t, r) -> printf "%s, %0.4f, %s" n t (show r)) summary
    (==0) <$> computeFailures smap




gitTimestamp :: IO String
gitTimestamp = do
   res <- gitProcess ["show", "--format=\"%ci\"", "--quiet"]
   return $ filter notNoise res

gitEpochTimestamp :: IO String
gitEpochTimestamp = do
   res <- gitProcess ["show", "--format=\"%ct\"", "--quiet"]
   return $ filter notNoise res

gitHash :: IO String
gitHash = do
   res <- gitProcess ["show", "--format=\"%H\"", "--quiet"]
   return $ filter notNoise res

gitRef :: IO String
gitRef = do
   res <- gitProcess ["show", "--format=\"%d\"", "--quiet"]
   return $ filter notNoise res

-- | Calls `git` for info; returns `"plain"` if we are not in a git directory.
gitProcess :: [String] -> IO String
gitProcess args = (readProcess "git" args []) `catchIOError` const (return "plain")

notNoise :: Char -> Bool
notNoise a = a /= '\"' && a /= '\n' && a /= '\r'

headerDelim :: String
headerDelim = replicate 80 '-'

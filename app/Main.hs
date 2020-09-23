
{-# LANGUAGE ScopedTypeVariables#-}
module Main where

import           System.Environment ( getArgs ) 
import           System.Exit ()
import           Control.Monad (void)
import qualified Language.Fixpoint.Types  as F 
import           Language.Sprite.Common   (crashUserError, doOrDie)
import           Language.Sprite.Common.UX ()
import qualified Language.Sprite.L1       as L1
import qualified Language.Sprite.L2       as L2
import qualified Language.Sprite.L3       as L3
import qualified Language.Sprite.L4       as L4
import qualified Language.Sprite.L5       as L5
import qualified Language.Sprite.L6       as L6
import qualified Language.Sprite.L8       as L8

---------------------------------------------------------------------------
main :: IO ()
---------------------------------------------------------------------------
main = do 
  args <- parseArgs
  case args of 
    Just (i, f) -> doOrDie (sprite i f)
    Nothing     -> crashUserError "Invalid options!" []

parseArgs :: IO (Maybe (Int, FilePath))
parseArgs = do
  args <- getArgs
  case args of 
    [f]   -> return $ Just (0, f)
    n:f:_ -> return $ Just (read n :: Int, f)
    _     -> return Nothing 

sprite :: Int -> FilePath -> IO ()
sprite 1 = L1.sprite
sprite 2 = L2.sprite
sprite 3 = L3.sprite
sprite 4 = L4.sprite
sprite 5 = L5.sprite
sprite 6 = L6.sprite
sprite _ = L8.sprite




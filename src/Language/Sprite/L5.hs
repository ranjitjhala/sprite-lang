module Language.Sprite.L5 ( sprite ) where

import           System.Exit
import qualified Language.Fixpoint.Types   as F
import           Language.Sprite.L5.Check
import           Language.Sprite.L5.Parse
import           Language.Sprite.Common

--------------------------------------------------------------------------------
sprite :: FilePath -> IO ()
--------------------------------------------------------------------------------
sprite f = do
  src <- parseFile f
  res <- case vcgen src of
           Left errs -> pure (crash errs "VCGen failure")
           Right vc  -> checkValid f vc
  ec  <- resultExit res
  exitWith ec

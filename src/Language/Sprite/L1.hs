module Language.Sprite.L1 ( sprite ) where

import           Control.Monad (void)
import           System.Exit
import qualified Language.Fixpoint.Types        as F
-- import qualified Language.Fixpoint.Types.Config as F
-- import qualified Language.Fixpoint.Misc         as F
-- import           Language.Sprite.L1.Types
import           Language.Sprite.L1.Check
import           Language.Sprite.L1.Parse
import           Language.Sprite.Common

sprite :: FilePath -> IO ()
sprite f = do
  src <- parseFile f
  -- print (void src)
  res <- case vcgen src of
           Left errs -> pure (crash errs "VCGen failure")
           Right vc  -> checkValid f vc
  ec  <- resultExit res
  exitWith ec

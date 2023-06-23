module Language.Sprite.L2 ( sprite ) where

import           System.Exit
import qualified Language.Fixpoint.Types        as F
import qualified Language.Fixpoint.Types.Config as F
import qualified Language.Fixpoint.Misc         as F
import           Language.Sprite.L2.Types
import           Language.Sprite.L2.Check
import           Language.Sprite.L2.Parse
import           Language.Sprite.Common
import Language.Sprite.Common.UX (crash)

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

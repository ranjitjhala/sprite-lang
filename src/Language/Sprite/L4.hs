module Language.Sprite.L4 ( sprite ) where
 
import           System.Exit 
import qualified Language.Fixpoint.Types        as F 
import           Language.Sprite.L4.Check 
import           Language.Sprite.L4.Parse 
import           Language.Sprite.Common 

--------------------------------------------------------------------------------
sprite :: FilePath -> IO ()
--------------------------------------------------------------------------------
sprite f = do
  src <- parseFile f
  res <- case vcgen src of 
           Left errs -> pure (F.Crash errs "VCGen failure") 
           Right vc  -> checkValid vc 
  ec  <- resultExit res
  exitWith ec

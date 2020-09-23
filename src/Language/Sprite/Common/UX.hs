-- | This module contains the code for all the user (programmer) facing
--   aspects, i.e. error messages, source-positions, overall results.

{-# LANGUAGE OverloadedStrings    #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE DeriveGeneric        #-}

module Language.Sprite.Common.UX
  (
  -- * Extraction from Source file
    readFileSpan

  -- * Constructing spans
  , posSpan
  , junkSpan

  -- * Success and Failure
  , UserError
  , eMsg
  , eSpan
  , Result

  -- * Throwing & Handling Errors
  , mkError
  , abort
  , panic
  , panicS
  , renderErrors
  , fpUserError

  -- * Pretty Printing
  , Text
  , PPrint (..)
  , tshow
  ) where

import           Control.Exception
import           Control.DeepSeq
import           Data.Typeable
-- import qualified Data.List as L
import           GHC.Generics
import           Text.Printf (printf)
import qualified Text.PrettyPrint.HughesPJ as PJ
import qualified Language.Fixpoint.Misc  as Misc
import qualified Language.Fixpoint.Types as F
import           Language.Fixpoint.Types (PPrint (..))
import           Language.Sprite.Common.Misc

type Text = PJ.Doc

tshow :: (Show a) => a -> PJ.Doc
tshow = PJ.text . show

--------------------------------------------------------------------------------
-- | Source Span Representation
--------------------------------------------------------------------------------

-- instance NFData F.SrcSpan 

instance Semigroup F.SrcSpan where
  (<>) = mappendSpan

instance Monoid F.SrcSpan where
  mempty = junkSpan

mappendSpan :: F.SrcSpan -> F.SrcSpan -> F.SrcSpan
mappendSpan s1 s2
  | s1 == junkSpan = s2
  | s2 == junkSpan = s1
  | otherwise      = F.SS (F.sp_start s1) (F.sp_stop s2)

spanInfo :: F.SrcSpan -> (FilePath, Int, Int, Int, Int)
spanInfo s    = (f, F.unPos l1, F.unPos c1, F.unPos l2, F.unPos c2)
  where
    (f,l1,c1) = F.sourcePosElts (F.sp_start s)
    (_,l2,c2) = F.sourcePosElts (F.sp_stop  s)

--------------------------------------------------------------------------------
-- | Source Span Extraction
--------------------------------------------------------------------------------
readFileSpan :: F.SrcSpan -> IO String
--------------------------------------------------------------------------------
readFileSpan sp = getSpan sp <$> readFile (spanFile sp)

spanFile :: F.SrcSpan -> FilePath
spanFile = Misc.fst3 . F.sourcePosElts . F.sp_start

getSpan :: F.SrcSpan -> String -> String
getSpan sp
  | l1 == l2  = getSpanSingle l1 c1 c2
  | otherwise = getSpanMulti  l1 l2
  where
    (_, l1, c1, l2, c2) = spanInfo sp

getSpanSingle :: Int -> Int -> Int -> String -> String
getSpanSingle l c1 c2
  = highlight l c1 c2
  . safeHead ""
  . getRange l l
  . lines

getSpanMulti :: Int -> Int -> String -> String
getSpanMulti l1 l2
  = highlights l1
  . getRange l1 l2
  . lines

highlight :: Int -> Int -> Int -> String -> String
highlight l c1 c2 s = unlines
  [ cursorLine l s
  , replicate (12 + c1) ' ' ++ replicate (1 + c2 - c1) '^'
  ]

highlights :: Int -> [String] -> String
highlights i ls = unlines $ zipWith cursorLine [i..] ls

cursorLine :: Int -> String -> String
cursorLine l s = printf "%s|  %s" (lineString l) s

lineString :: Int -> String
lineString n = replicate (10 - nD) ' ' ++ nS
  where
    nS       = show n
    nD       = length nS

--------------------------------------------------------------------------------
-- | Source Span Construction
--------------------------------------------------------------------------------
posSpan :: F.SourcePos -> F.SrcSpan
--------------------------------------------------------------------------------
posSpan p = F.SS p p

junkSpan :: F.SrcSpan
junkSpan = F.dummySpan -- posSpan (initialPos "unknown")

--------------------------------------------------------------------------------
-- | Representing overall failure / success
--------------------------------------------------------------------------------
type Result a = Either [UserError] a

--------------------------------------------------------------------------------
-- | Representing (unrecoverable) failures
--------------------------------------------------------------------------------
data UserError = Error
  { eMsg  :: !Text
  , eSpan :: !F.SrcSpan
  }
  deriving (Show, Typeable, Generic)

instance F.PPrint UserError where 
  pprintTidy k = F.pprintTidy k . userErrorFP 

instance F.Fixpoint UserError where 
  toFix = eMsg 

instance F.Loc UserError where 
  srcSpan = eSpan

instance NFData UserError 
instance Exception [UserError]

fpUserError :: F.Error1 -> UserError
fpUserError e = mkError (F.errMsg e) (F.errLoc e)

userErrorFP :: UserError -> F.Error 
userErrorFP (Error d sp) = F.err sp d 

--------------------------------------------------------------------------------
panic :: PJ.Doc -> F.SrcSpan -> a
--------------------------------------------------------------------------------
panic msg sp = throw [Error msg sp]

panicS :: String -> F.SrcSpan -> a
panicS = panic . PJ.text

--------------------------------------------------------------------------------
abort :: UserError -> b
--------------------------------------------------------------------------------
abort e = throw [e]

--------------------------------------------------------------------------------
mkError :: Text -> F.SrcSpan -> UserError
--------------------------------------------------------------------------------
mkError = Error

renderErrors :: [UserError] -> IO Text
renderErrors es = do
  errs  <- mapM renderError es
  return $ PJ.vcat ("Errors found!" : "" : errs)
--  return $ L.intercalate "\n" ("Errors found!" : errs)

renderError :: UserError -> IO Text
renderError e = do
  let sp   = F.srcSpan e
  snippet <- readFileSpan sp
  return   $ PJ.vcat [ F.pprint sp PJ.<> ":" PJ.<+> (eMsg e) 
                     , " "
                     , " "
                     , PJ.text snippet ] 


 

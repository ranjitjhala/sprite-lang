module Language.Sprite.Common.Parse where

import qualified Data.Maybe               as Mb
import qualified Data.Set                 as S
import qualified Language.Fixpoint.Types  as F
import qualified Language.Fixpoint.Parse  as FP
import qualified Language.Fixpoint.Types.Visitor as FV
import Text.Megaparsec                    ( (<|>) )

withSpan' :: FP.Parser (F.SrcSpan -> a) -> FP.Parser a
withSpan' p = do
  F.Loc l1 l2 f <- FP.located p
  pure (f (F.SS l1 l2))

-- | `identifier` parses identifiers: lower-case alphabets followed by alphas or digits
identifier :: FP.Parser F.Symbol
identifier = FP.lowerIdP

identifier' :: FP.Parser F.Symbol
identifier' = FP.lowerIdP <|> FP.upperIdP

parens = FP.parens
colon = FP.colon
comma = FP.comma
braces = FP.braces
reserved = FP.reserved
brackets = FP.brackets
whiteSpace = FP.spaces
reservedOp = FP.reservedOp

-- | list of reserved words
keywords :: S.Set String 
keywords = S.fromList
  [ "if"      , "else"
  , "true"    , "false"
  , "let"     , "in"
  , "int"
  ]

isKey :: String -> Bool
isKey x = S.member x keywords


---------------------------------------------------------------------------------------------------------
-- | Pesky hack to work around FP.exprP parsing  "foo(x, y, z)" as "foo ((,,) x y z)"
---------------------------------------------------------------------------------------------------------
myPredP :: FP.Parser F.Expr
myPredP = unTupleApp <$> FP.predP

myExprP :: FP.Parser F.Expr
myExprP = unTupleApp <$> FP.exprP 

unTupleApp :: F.Expr -> F.Expr
unTupleApp = FV.mapExpr go
  where
    go e@(F.EApp {}) = Mb.fromMaybe e (unTuple e)
    go e = e 

unTuple :: F.Expr -> Maybe F.Expr
unTuple e = 
  case F.splitEApp e of
    (f, [arg]) -> 
      case F.splitEApp arg of
        (t, args) -> if isTupleCon (length args) t 
                     then Just (F.eApps f args)
                     else Nothing
    _ -> Nothing

isTupleCon :: Int -> F.Expr -> Bool
isTupleCon n (F.EVar x) = x == tupleSym n
isTupleCon _ _          = False 

tupleSym :: Int -> F.Symbol
tupleSym n = F.symbol $ "(" ++ replicate (n-1) ',' ++ ")"  
---------------------------------------------------------------------------------------------------------

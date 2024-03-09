{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections     #-}

module Language.Sprite.L1.Parse
  (
    -- * Parsing programs
      parseFile
    , parseWith

    -- * Parsing combinators
    , rtype
    , expr
  ) where

import qualified Data.Set                 as S
import qualified Data.List                as L
import           Control.Monad.Combinators.Expr
import           Text.Megaparsec       hiding (State, label)
import           Text.Megaparsec.Char
import qualified Language.Fixpoint.Types  as F
import qualified Language.Fixpoint.Parse  as FP
import           Language.Sprite.Common
import           Language.Sprite.Common.Parse
import qualified Language.Sprite.Common.UX as UX
import           Language.Sprite.L1.Types

parseFile :: FilePath -> IO SrcExpr
parseFile = FP.parseFromFile prog

parseWith :: FP.Parser a -> FilePath -> String -> a
parseWith = FP.doParse'

--------------------------------------------------------------------------------
-- | Top-Level Expression Parser
--------------------------------------------------------------------------------
prog :: FP.Parser SrcExpr
prog = declsExpr <$> many decl

expr :: FP.Parser SrcExpr
expr = makeExprParser expr1 binOps

binOps =
  [ [InfixR  (FP.reservedOp "*"    >> pure (op BTimes)) ]
  , [InfixR  (FP.reservedOp "+"    >> pure (op BPlus))  ]
  , [InfixL  (FP.reservedOp "-"    >> pure (op BMinus)) ]
  ]

op :: PrimOp -> SrcExpr -> SrcExpr -> SrcExpr
op o e1 e2 = case (e1, e2) of
  (EImm x lx, EImm y ly) -> mkEApp (EImm (ECon (PBin o) l) l) [x, y]
  _                      -> UX.panic "Prim-Ops only on variables" l
  where
    l = stretch [e1, e2]

mkEApp :: SrcExpr -> [SrcImm] -> SrcExpr
mkEApp = L.foldl' (\e y -> EApp e y (label e <> label y))

expr1 :: FP.Parser SrcExpr
expr1 =  try appExpr
     <|> expr0

expr0 :: FP.Parser SrcExpr
expr0 =  try funExpr
     <|> letExpr
     -- <|> try ifExpr
     <|> FP.parens expr
     <|> FP.braces expr
     <|> immExpr

letExpr :: FP.Parser SrcExpr
letExpr = withSpan' (ELet <$> decl <*> expr)

immExpr :: FP.Parser SrcExpr
immExpr = do
  i <- imm
  return (EImm i (label i))

imm :: FP.Parser SrcImm
imm =  withSpan' $ (EVar <$> identifier) <|> (ECon . PInt <$> FP.natural   )

funExpr :: FP.Parser SrcExpr
funExpr = withSpan' $ do
  xs    <- FP.parens (sepBy1 binder FP.comma)
  _     <- FP.reservedOp "=>"
  body  <- expr
  return $ mkEFun xs body

mkEFun :: [SrcBind] -> SrcExpr -> F.SrcSpan -> SrcExpr
mkEFun bs e0 l = foldr (\b e -> EFun b e l) e0 bs

appExpr :: FP.Parser SrcExpr
appExpr = mkEApp <$> expr0 <*> FP.parens (sepBy1 imm FP.comma)

-- | Annotated declaration
decl :: FP.Parser SrcDecl
decl = mkDecl <$> ann <*> plainDecl


type Ann = Maybe (F.Symbol, RType)

ann :: FP.Parser Ann
-- ann = (FP.reservedOp "/*@" >> (Just <$> annot)) <|> pure Nothing
ann = (FP.reserved "/*@" >> (Just <$> annot)) <|> pure Nothing

annot :: FP.Parser (F.Symbol, RType)
annot = do
  FP.reserved "val"
  x <- FP.lowerIdP
  FP.colon
  t <- rtype
  FP.reservedOp "*/"
  return (x, t)

mkDecl :: Ann -> SrcDecl -> SrcDecl
mkDecl (Just (x, t)) (Decl b e l)
  | x == bindId b    = Decl b (EAnn e t (label e)) l
  | otherwise        = error $ "bad annotation: " ++ show (x, bindId b)
mkDecl Nothing    d  = d

plainDecl :: FP.Parser SrcDecl
plainDecl = withSpan' $ do
  FP.reserved "let"
  b <- binder
  FP.reservedOp "="
  e <- expr
  FP.semi
  return (Decl b e)

-- | `binder` parses SrcBind, used for let-binds and function parameters.
binder :: FP.Parser SrcBind
binder = withSpan' (Bind <$> identifier)

pairSpan :: FP.Parser a -> FP.Parser (a, F.SrcSpan)
pairSpan p = withSpan' $ do
  x <- p
  return (x,)

isKey :: String -> Bool
isKey x = S.member x keywords

stretch :: (Label t, Monoid a) => [t a] -> a
stretch = mconcat . fmap label

--------------------------------------------------------------------------------
-- | Top level Rtype parser
--------------------------------------------------------------------------------
rtype :: FP.Parser RType
rtype =  try rfun
     <|> rtype0

rtype0 :: FP.Parser RType
rtype0 = FP.parens rtype
      <|> rbase

rfun :: FP.Parser RType
rfun  = mkTFun <$> funArg <*> (FP.reservedOp "=>" *> rtype)

funArg :: FP.Parser (F.Symbol, RType)
funArg = try ((,) <$> FP.lowerIdP <*> (FP.colon *> rtype0))
      <|> ((,) <$> freshArgSymbolP <*> rtype0)

freshArgSymbolP :: FP.Parser F.Symbol
freshArgSymbolP = do
  n <- FP.freshIntP
  return $ F.symbol ("_arg" ++ show n)

mkTFun :: (F.Symbol, RType) -> RType -> RType
mkTFun (x, s) = TFun x s

rbase :: FP.Parser RType
rbase = TBase <$> tbase <*> refTop

tbase :: FP.Parser Base
tbase = FP.reserved "int" >> pure TInt

refTop :: FP.Parser F.Reft
refTop = FP.brackets reftB <|> pure mempty

reftB :: FP.Parser F.Reft
reftB = mkReft <$> (FP.lowerIdP <* mid) <*> FP.predP

mkReft :: F.Symbol -> F.Pred -> F.Reft
mkReft x r = F.Reft (x, r)

mid :: FP.Parser ()
mid = FP.reservedOp "|"

-- >>> (parseWith rtype "" "int{v|v = 3}")
-- TBase TInt (v = 3)

-- >>> (parseWith rtype "" "int{v|v = x + y}")
-- TBase TInt (v = (x + y))

-- >>> (parseWith rtype "" "int")
-- TBase TInt true

-- >>> parseWith funArg "" "x:int"
-- ("x",TBase TInt true)

-- >>> parseWith rfun "" "int => int"
-- TFun "_" (TBase TInt true) (TBase TInt true)

-- >>> parseWith rfun "" "x:int => int"
-- TFun "x" (TBase TInt true) (TBase TInt true)

-- >>> parseWith rfun "" "x:int => int{v|0 < v}"
-- TFun "x" (TBase TInt true) (TBase TInt (0 < v))

-- >>> parseWith rfun "" "x:int => int{v|0 <= v}"
-- TFun "x" (TBase TInt true) (TBase TInt (0 <= v))

-- >>> parseWith rfun "" "x:int{v|0 <= v} => int{v|0 <= v}"
-- TFun "x" (TBase TInt (0 <= v)) (TBase TInt (0 <= v))

-- >>> parseWith ann "" "/*@ val inc: x:int => int[v|v = x + 1] */"
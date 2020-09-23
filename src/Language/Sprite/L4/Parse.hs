{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections     #-}

module Language.Sprite.L4.Parse 
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
import           Language.Sprite.L4.Types hiding (immExpr)
import           Language.Sprite.L4.Constraints

parseFile :: FilePath -> IO ([F.Qualifier], SrcExpr)
parseFile = FP.parseFromFile prog 

parseWith :: FP.Parser a -> FilePath -> String -> a
parseWith = FP.doParse'

--------------------------------------------------------------------------------
-- | Top-Level Expression Parser
--------------------------------------------------------------------------------
prog :: FP.Parser ([F.Qualifier], SrcExpr)
prog = do 
  qs  <- quals
  src <- declsExpr <$> many decl
  return (qs, src)

quals :: FP.Parser [F.Qualifier]
quals =  try ((:) <$> between annL annR qual <*> quals) 
     <|> pure []

qual ::FP.Parser F.Qualifier
qual = reserved "qualif" >> FP.qualifierP (baseSort <$> tbase)

expr :: FP.Parser SrcExpr
expr =  try funExpr
    <|> try letExpr
    <|> try ifExpr
    <|> try (FP.braces (expr <* whiteSpace))
    <|> try appExpr 
    <|> try binExp
    <|> expr0

expr0 :: FP.Parser SrcExpr   
expr0 =  try (FP.parens expr)
     <|> immExpr

appExpr :: FP.Parser SrcExpr
appExpr = mkEApp <$> immExpr <*> parens (sepBy1 imm comma)

binExp :: FP.Parser SrcExpr
binExp = withSpan' $ do
  x <- imm 
  o <- op
  y <- imm
  return (bop o x y) 

op :: FP.Parser PrimOp 
op =  (FP.reservedOp "*"    >> pure BTimes)
  <|> (FP.reservedOp "+"    >> pure BPlus )
  <|> (FP.reservedOp "-"    >> pure BMinus)
  <|> (FP.reservedOp "<"    >> pure BLt   )  
  <|> (FP.reservedOp "<="   >> pure BLe   )  
  <|> (FP.reservedOp "=="   >> pure BEq   )  
  <|> (FP.reservedOp ">"    >> pure BGt   )  
  <|> (FP.reservedOp ">="   >> pure BGe   )  
  <|> (FP.reservedOp "&&"   >> pure BOr   )  
  <|> (FP.reservedOp "||"   >> pure BOr   )  

bop :: PrimOp -> SrcImm -> SrcImm -> F.SrcSpan -> SrcExpr
bop o x y l = mkEApp (EImm (ECon (PBin o) l) l) [x, y]

mkEApp :: SrcExpr -> [SrcImm] -> SrcExpr
mkEApp = L.foldl' (\e y -> EApp e y (label e <> label y))


letExpr :: FP.Parser SrcExpr 
letExpr = withSpan' (ELet <$> decl <*> expr)

ifExpr :: FP.Parser SrcExpr
ifExpr = withSpan' $ do 
  FP.reserved "if"
  v <- parens imm 
  e1 <- expr 
  FP.reserved "else"
  e2 <- expr
  return (EIf v e1 e2) 

immExpr :: FP.Parser SrcExpr
immExpr = do 
  i <- imm 
  return (EImm i (label i))

imm :: FP.Parser SrcImm
imm = immInt <|> immBool <|> immId 

immInt :: FP.Parser SrcImm
immInt = withSpan' (ECon . PInt  <$> FP.natural)
       
immBool :: FP.Parser SrcImm
immBool = withSpan' (ECon . PBool <$> bool)  

immId :: FP.Parser SrcImm
immId = withSpan' (EVar <$> identifier)  

bool :: FP.Parser Bool 
bool = (reserved "true"  >> pure True)
    <|>(reserved "false" >> pure False) 

funExpr :: FP.Parser SrcExpr
funExpr = withSpan' $ do 
  xs    <- parens (sepBy1 binder comma) 
  _     <- FP.reservedOp "=>"
  -- _     <- FP.reservedOp "{"
  body  <- braces (expr <* whiteSpace)
  -- _     <- FP.reservedOp "}"
  return $ mkEFun xs body

mkEFun :: [SrcBind] -> SrcExpr -> F.SrcSpan -> SrcExpr
mkEFun bs e0 l = foldr (\b e -> EFun b e l) e0 bs 

-- | Annotated declaration
decl :: FP.Parser SrcDecl 
decl = mkDecl <$> ann <*> plainDecl

type Ann = Maybe (F.Symbol, RType)

annL, annR :: FP.Parser ()
annL = reservedOp "/*@"
annR = reservedOp "*/" 

ann :: FP.Parser Ann
ann = (annL >> (Just <$> annot)) <|> pure Nothing

annot :: FP.Parser (F.Symbol, RType)
annot = do
  reserved "val"
  x <- FP.lowerIdP
  colon
  t <- rtype
  annR 
  return (x, t)

{-
between :: FP.Parser () -> FP.Parser () -> FP.Parser a -> FP.Parser a
between lP rP xP =  do 
  lP
  x <- xP
  rP
  return x
 -}
mkDecl :: Ann -> SrcDecl -> SrcDecl 
mkDecl (Just (x, t)) (Decl b e l) 
  | x == bindId b    = Decl b (EAnn  e (generalize t) (label e)) l 
  | otherwise        = error $ "bad annotation: " ++ show (x, bindId b) 
mkDecl (Just (x, t)) (RDecl b e l) 
  | x == bindId b    = RDecl b (EAnn e (generalize t) (label e)) l 
  | otherwise        = error $ "bad annotation: " ++ show (x, bindId b) 
mkDecl Nothing    d  = d

plainDecl :: FP.Parser SrcDecl
plainDecl = withSpan' $ do
  ctor <- (FP.reserved "let rec" >> pure RDecl) <|>
          (FP.reserved "let"     >> pure Decl) 
  b    <- binder 
  FP.reservedOp "="
  e    <- expr 
  FP.semi 
  return (ctor b e) 

-- | `binder` parses SrcBind, used for let-binds and function parameters.
binder :: FP.Parser SrcBind
binder = withSpan' (Bind <$> identifier)

--------------------------------------------------------------------------------
-- | Top level Rtype parser 
--------------------------------------------------------------------------------
rtype :: FP.Parser RType
rtype =  try rfun <|> rtype0

rtype0 :: FP.Parser RType
rtype0 = parens rtype 
      <|> rbase 

rfun :: FP.Parser RType
rfun  = mkTFun <$> funArg <*> (FP.reservedOp "=>" *> rtype)

funArg :: FP.Parser (F.Symbol, RType)
funArg = try ((,) <$> FP.lowerIdP <*> (colon *> rtype0))
      <|> ((junkSymbol,) <$> rtype0)

mkTFun :: (F.Symbol, RType) -> RType -> RType
mkTFun (x, s) = TFun x s 

rbase :: FP.Parser RType
rbase = TBase <$> tbase <*> refTop

tbase :: FP.Parser Base
tbase =  (reserved "int"  >>  pure TInt)
     <|> (reserved "bool" >>  pure TBool)
     <|> tvarP 

tvarP :: FP.Parser Base 
tvarP = FP.reservedOp "'" >> FP.lowerIdP  >>= return . TVar . TV 

-- tVar :: F.Symbol -> Base
-- tVar = TVar . TV

refTop :: FP.Parser Reft
refTop = brackets reftB <|> pure mempty 

reftB :: FP.Parser Reft
reftB =  (question >> pure Unknown) 
     <|> KReft <$> (FP.lowerIdP <* mid) <*> FP.predP

mid :: FP.Parser ()
mid = FP.reservedOp "|"

question :: FP.Parser ()
question = FP.reservedOp "?"

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


-- | list of reserved words
keywords :: S.Set String 
keywords = S.fromList
  [ "if"      , "else"
  , "true"    , "false"
  , "let"     , "in"
  , "int"
  ]

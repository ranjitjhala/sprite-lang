{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections     #-}

module Language.Sprite.L5.Parse
  (
    -- * Parsing programs
      parseFile
    , parseWith

    -- * Parsing combinators
    , measureP
    , rtype
    , expr
    , typP
    , switchExpr
    , altP
  ) where

import qualified Data.Maybe               as Mb
import qualified Data.Set                 as S
import qualified Data.List                as L
import           Control.Monad.Combinators.Expr
import           Text.Megaparsec       hiding (State, label)
import           Text.Megaparsec.Char
import qualified Language.Fixpoint.Types  as F
import qualified Language.Fixpoint.Parse  as FP
import           Language.Sprite.Common
import           Language.Sprite.Common.Parse
import qualified Language.Sprite.Common.Misc as Misc
import           Language.Sprite.L5.Types hiding (immExpr)
import Language.Sprite.Common.Constraints
-- import           Language.Sprite.L5.Constraints

parseFile :: FilePath -> IO SrcProg
parseFile = FP.parseFromFile prog

parseWith :: FP.Parser a -> FilePath -> String -> a
parseWith = FP.doParse'

--------------------------------------------------------------------------------
-- | Top-Level Expression Parser
--------------------------------------------------------------------------------
prog :: FP.Parser SrcProg
prog = do
  qs   <- quals
  ms   <- try (many measureP) <|> return []
  typs <- many typP
  src  <- declsExpr <$> many decl
  return (Prog qs ms src (Misc.traceShow "prog-types" typs))

measureP :: FP.Parser (F.Symbol, F.Sort)
measureP = annL >> (Misc.mapSnd (rTypeSort . generalize) <$> tyBindP "measure")

typP :: FP.Parser SrcData
typP = do
  reserved "type"
  tc    <- FP.lowerIdP
  args  <- typArgs
  (FP.reservedOp "=" >> whiteSpace)
  ctors <- ctorsP
  return (Data tc args (mkCtor tc args <$> ctors))

data Ctor   = Ctor SrcBind [FunArg] (Maybe Reft)
type FunArg = (F.Symbol, RType)

ctorsP :: FP.Parser [Ctor]
ctorsP = try (FP.semi >> return [])
      <|> (:) <$> ctorP <*> ctorsP

ctorP :: FP.Parser Ctor
ctorP = Ctor <$> (whiteSpace *> mid *> cbind) <*> commaList funArgP <*> ctorResP

cbind :: FP.Parser SrcBind
cbind = withSpan' (Bind <$> FP.upperIdP)

typArgs :: FP.Parser [F.Symbol]
typArgs = commaList tvarP

ctorResP :: FP.Parser (Maybe Reft)
ctorResP =  Just <$> (FP.reservedOp "=>" *> brackets concReftB)
        <|> return Nothing

mkCtor :: Ident -> [Ident] -> Ctor -> (SrcBind, RType)
mkCtor tc args c  = (dc, generalize dcType)
  where
    dcType        = foldr (\(x, t) s -> TFun x t s) dcRes xts
    dcRes         = TCon tc (rVar <$> args) dcReft
    Ctor dc xts r = c
    dcReft        = Mb.fromMaybe mempty r

commaList :: FP.Parser a -> FP.Parser [a]
commaList p = try (parens (sepBy p comma)) <|> return []

quals :: FP.Parser [F.Qualifier]
quals =  try ((:) <$> between annL annR qual <*> quals)
     <|> pure []

qual ::FP.Parser F.Qualifier
qual = reserved "qualif" >> FP.qualifierP (rTypeSort <$> rtype)

expr :: FP.Parser SrcExpr
expr =  try funExpr
    <|> try letExpr
    <|> try ifExpr
    <|> try switchExpr
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
  <|> (FP.reservedOp "&&"   >> pure BAnd  )
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

switchExpr :: FP.Parser SrcExpr
switchExpr = withSpan' $ do
  FP.reserved "switch"
  x    <- parens FP.lowerIdP
  alts <- braces (many altP)
  return (ECase x alts)

altP :: FP.Parser SrcAlt
altP = withSpan' $ Alt
         <$> (whiteSpace *> mid *> FP.upperIdP)
         -- <*> pure Nothing
         <*> commaList binder
         <*> (FP.reservedOp "=>" *> expr)

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
immId = withSpan' (EVar <$> identifier')

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
  where
    ann = (annL >> (Just <$> tyBindP "val")) <|> pure Nothing

type Ann = Maybe (F.Symbol, RType)

annL, annR :: FP.Parser ()
annL = reservedOp "/*@"
annR = reservedOp "*/"

tyBindP :: String -> FP.Parser (F.Symbol, RType)
tyBindP kw = do
  reserved kw
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
rfun  = mkTFun <$> funArgP <*> (FP.reservedOp "=>" *> rtype)

funArgP :: FP.Parser FunArg
funArgP = try ((,) <$> FP.lowerIdP <*> (colon *> rtype0))
      <|> ((\i t -> (anon i, t)) <$> FP.freshIntP <*> rtype0)

mkTFun :: (F.Symbol, RType) -> RType -> RType
mkTFun (x, s) = TFun x s

rbase :: FP.Parser RType
rbase =  try (TBase <$> tbase <*> refTop)
     <|> TCon <$> identifier' <*> commaList rtype <*> refTop

tbase :: FP.Parser Base
tbase =  (reserved "int"  >>  pure TInt)
     <|> (reserved "bool" >>  pure TBool)
     <|> (tvarP >>= return . TVar. TV)

tvarP :: FP.Parser F.Symbol
tvarP = FP.reservedOp "'" >> FP.lowerIdP  -- >>= return . TVar . TV

refTop :: FP.Parser Reft
refTop = brackets reftB <|> pure mempty

reftB :: FP.Parser Reft
reftB =  (question >> pure Unknown)
     <|> concReftB

concReftB :: FP.Parser Reft
concReftB = KReft <$> (FP.lowerIdP <* mid) <*> myPredP

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
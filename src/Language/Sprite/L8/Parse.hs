{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TupleSections     #-}

module Language.Sprite.L8.Parse
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
import qualified Language.Fixpoint.Horn.Types  as H
import           Language.Sprite.Common
import qualified Language.Sprite.Common.Misc as Misc
import           Language.Sprite.Common.Parse

import           Language.Sprite.L8.Types hiding (rVarARef, immExpr)
import Language.Sprite.Common.Constraints
-- import           Language.Sprite.L8.Constraints

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
  ms   <- (try (many measureP)) <|> return []
  typs <- many typP
  src  <- declsExpr <$> many decl
  return (Prog qs ms src typs)

measureP :: FP.Parser (F.Symbol, F.Sort)
measureP = annL >> (Misc.mapSnd (rTypeSort . generalize) <$> tyBindP "measure")

typP :: FP.Parser SrcData
typP = do
  FP.reserved "type"
  tc    <- FP.lowerIdP
  tvars <- typArgs
  rvars <- commaList refVar
  inv   <- refTop
  (FP.reservedOp "=" >> FP.spaces)
  ctors <- fmap (mkCtor tc tvars rvars) <$> ctorsP
  return (Data tc tvars rvars ctors inv)

data Ctor   = Ctor SrcBind [FunArg] (Maybe Reft)
type FunArg = (F.Symbol, RType)

ctorsP :: FP.Parser [Ctor]
ctorsP = try (FP.semi >> return [])
      <|> (:) <$> ctorP <*> ctorsP

ctorP :: FP.Parser Ctor
ctorP = Ctor <$> (FP.spaces *> mid *> cbind) <*> commaList funArgP <*> ctorResP

cbind :: FP.Parser SrcBind
cbind = withSpan' (Bind <$> FP.upperIdP)

typArgs :: FP.Parser [F.Symbol]
typArgs = commaList tvarP

ctorResP :: FP.Parser (Maybe Reft)
ctorResP =  Just <$> (FP.reservedOp "=>" *> FP.brackets concReftB)
        <|> return Nothing

mkCtor :: Ident -> [Ident] -> [RVar] -> Ctor -> (SrcBind, RType)
mkCtor tc tvs rvs c  = (dc, closeType rvs xts dcRes)
  where
    -- dcType        = foldr (\(x, t) s -> TFun x t s) dcRes xts
    dcRes         = TCon tc (rVar <$> tvs) (rVarARef <$> rvs) dcReft
    Ctor dc xts r = c
    dcReft        = Mb.fromMaybe mempty r

closeType :: [RVar] -> [(F.Symbol, RType)] -> RType -> RType
closeType rvs xts = tyParams
                  . rvarParams
                  . valParams
   where
     tyParams     = generalize
     rvarParams t = foldr TRAll t rvs
     valParams ty = foldr (\(x, t) s -> TFun x t s) ty xts

rVarARef :: RVar -> RARef
rVarARef (RVar p ts) = ARef xts (predReft pred)
  where
    xts  = zipWith (\t i -> (F.intSymbol "rvTmp" i, t)) ts [0..]
    pred = F.eApps (F.expr p) (F.expr . fst <$> xts)

commaList :: FP.Parser a -> FP.Parser [a]
commaList p = try (FP.parens (sepBy p FP.comma)) <|> return []

quals :: FP.Parser [F.Qualifier]
quals =  try ((:) <$> between annL annR qual <*> quals)
     <|> pure []

qual ::FP.Parser F.Qualifier
qual = FP.reserved "qualif" >> FP.qualifierP (rTypeSort <$> rtype)

expr :: FP.Parser SrcExpr
expr =  try funExpr
    <|> try letExpr
    <|> try ifExpr
    <|> try switchExpr
    <|> try (FP.braces (expr <* FP.spaces))
    <|> try appExpr
    <|> try binExp
    <|> expr0

expr0 :: FP.Parser SrcExpr
expr0 =  try (FP.parens expr)
     <|> immExpr

appExpr :: FP.Parser SrcExpr
appExpr = mkEApp <$> immExpr <*> FP.parens (sepBy1 imm FP.comma)

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
  v <- FP.parens imm
  e1 <- expr
  FP.reserved "else"
  e2 <- expr
  return (EIf v e1 e2)

switchExpr :: FP.Parser SrcExpr
switchExpr = withSpan' $ do
  FP.reserved "switch"
  x    <- FP.parens FP.lowerIdP
  alts <- FP.braces (many altP)
  return (ECase x alts)

altP :: FP.Parser SrcAlt
altP = withSpan' $ Alt
         <$> (FP.spaces *> mid *> FP.upperIdP)
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
bool = (FP.reserved "true"  >> pure True)
    <|>(FP.reserved "false" >> pure False)

funExpr :: FP.Parser SrcExpr
funExpr = withSpan' $ do
  xs    <- FP.parens (sepBy1 binder FP.comma)
  _     <- FP.reservedOp "=>"
  -- _     <- FP.reservedOp "{"
  body  <- FP.braces (expr <* FP.spaces)
  -- _     <- FP.reservedOp "}"
  return $ mkEFun xs body

mkEFun :: [SrcBind] -> SrcExpr -> F.SrcSpan -> SrcExpr
mkEFun bs e0 l = foldr (\b e -> EFun b e l) e0 bs

-- | Annotated declaration
decl :: FP.Parser SrcDecl
decl = do
  sig  <- try (Just <$> ann) <|> pure Nothing
  decl <- plainDecl
  case sig of
    Just (a, s) -> return (mkDecl a s decl)
    Nothing     -> return decl

ann :: FP.Parser (Ann, Sig)
ann =  annL >> (((Val,)  <$> sigP "val")
                <|>
                ((Refl,) <$> sigP "reflect"))

annL, annR :: FP.Parser ()
annL = FP.reservedOp "/*@"
annR = FP.reservedOp "*/"

sigP :: String -> FP.Parser Sig
sigP kw = do
  FP.reserved kw
  x <- FP.lowerIdP
  FP.colon
  t <- rtype
  m <- try (Just <$> metricP) <|> pure Nothing
  annR
  return (x, t, m)

metricP :: FP.Parser Metric
metricP = reserved "/" *> sepBy myExprP FP.comma


tyBindP :: String -> FP.Parser (F.Symbol, RType)
tyBindP kw = do
  (x, t, _) <- sigP kw
  return (x, t)

genSig :: Sig -> Sig
genSig (x, t, y) = (x, generalize t, y)

sigId :: Sig -> Ident
sigId (x, _, _) = x

mkDecl :: Ann -> Sig -> SrcDecl -> SrcDecl
mkDecl a s (Let b e l)
  | sigId s == bindId b = Let b (EAnn e a (genSig s) (label e)) l
mkDecl a s  (Rec b e l)
  | sigId s == bindId b = Rec b (EAnn e a (genSig s) (label e)) l
mkDecl _ s d
  | otherwise           = error $ "bad annotation: " ++ show (sigId s, bindId (declBind d))


plainDecl :: FP.Parser SrcDecl
plainDecl = withSpan' $ do
  ctor <- (FP.reserved "let rec" >> pure Rec) <|>
          (FP.reserved "let"     >> pure Let)
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
rtype =  (FP.reserved "forall" >> rall)
     <|> try rfun
     <|> rtype0

rtype0 :: FP.Parser RType
rtype0 = FP.parens rtype
      <|> rbase

rfun :: FP.Parser RType
rfun  = mkTFun <$> funArgP <*> (FP.reservedOp "=>" *> rtype)

rall :: FP.Parser RType
rall = TRAll <$> FP.parens refVar <*> (FP.dot *> rtype)

refVar :: FP.Parser RVar
refVar = mkRVar <$> FP.lowerIdP <*> (FP.colon *> rtype)

mkRVar :: F.Symbol -> RType -> RVar
mkRVar p t
  | isBool out = RVar p [ const () <$> s | (_, s) <- xs ]
  | otherwise  = error "Refinement variable must have `bool` as output type"
  where
    (xs, out)  = bkFun t

isBool :: RType -> Bool
isBool t = rTypeSort t == F.boolSort

funArgP :: FP.Parser FunArg
funArgP = try ((,) <$> FP.lowerIdP <*> (FP.colon *> rtype0))
      <|> ((\i t -> (anon i, t)) <$> FP.freshIntP <*> rtype0)

mkTFun :: (F.Symbol, RType) -> RType -> RType
mkTFun (x, s) = TFun x s

rbase :: FP.Parser RType
rbase =  try (TBase <$> tbase <*> refTop)
     <|> TCon <$> identifier' <*> commaList rtype <*> tConARefs <*> refTop

tbase :: FP.Parser Base
tbase =  (FP.reserved "int"  >>  pure TInt)
     <|> (FP.reserved "bool" >>  pure TBool)
     <|> (tvarP >>= return . TVar. TV)

tConARefs :: FP.Parser [RARef]
tConARefs = try (commaList aRef)
         <|> pure []

tvarP :: FP.Parser F.Symbol
tvarP = FP.reservedOp "'" >> FP.lowerIdP

refTop :: FP.Parser Reft
refTop = FP.brackets reftB <|> pure mempty

reftB :: FP.Parser Reft
reftB =  (question >> pure Unknown)
     <|> concReftB

concReftB :: FP.Parser Reft
concReftB = KReft <$> (FP.lowerIdP <* mid) <*> myPredP

aRef :: FP.Parser (ARef Reft)
aRef = ARef <$> commaList aRefArg <* FP.reservedOp "=>" <*> aRefBody
  where
    aRefArg :: FP.Parser (F.Symbol, RSort)
    aRefArg = (,) <$> FP.lowerIdP <* FP.colon <*> rSortP

aRefBody :: FP.Parser Reft
aRefBody = predReft <$> myPredP

predReft :: F.Pred -> Reft
predReft = Known F.dummySymbol . H.Reft

rSortP :: FP.Parser RSort
rSortP = rTypeToRSort <$> rtype0

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

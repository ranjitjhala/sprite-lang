{-# LANGUAGE DeriveFunctor     #-}
{-# LANGUAGE PatternSynonyms   #-}
{-# LANGUAGE OverloadedStrings #-}

module Language.Sprite.L3.Types where

import qualified Language.Fixpoint.Horn.Types  as H
import qualified Language.Fixpoint.Types       as F
-- import           Language.Sprite.Common.Misc
import           Language.Sprite.Common

-- | Basic types --------------------------------------------------------------

data Base = TInt | TBool
  deriving (Eq, Ord, Show)

-- | Refined Types ------------------------------------------------------------

data Type r
  = TBase !Base r                               -- ^ Int{r}
  | TFun  !F.Symbol !(Type r) !(Type r)         -- ^ x:s -> t
  deriving (Eq, Ord, Show)

rInt :: RType
rInt = TBase TInt mempty

rBool :: RType
rBool = TBase TBool mempty

data Reft
  = Known !F.Symbol !H.Pred   -- ^ Known refinement
  | Unknown                   -- ^ Unknown, to-be-synth refinement
  deriving (Show)

known :: F.Reft -> Reft
known (F.Reft (v, r)) = KReft v r

pattern KReft v p = Known v (H.Reft p)

instance Semigroup Reft where
  Unknown  <> r              = r
  r        <> Unknown        = r
  KReft v1 r1 <> KReft v2 r2 = KReft v r
    where F.Reft (v, r) = F.Reft (v1, r1) <> F.Reft (v2, r2)


instance Monoid Reft where
  mempty = KReft v r where F.Reft (v, r) = mempty

type RType = Type Reft

-- | Primitive Constants ------------------------------------------------------

data PrimOp
  = BPlus
  | BMinus
  | BTimes
  | BLt
  | BLe
  | BEq
  | BGt
  | BGe
  | BAnd
  | BOr
  | BNot
  deriving (Eq, Ord, Show)

data Prim
  = PInt  !Integer                    -- 0,1,2,...
  | PBool !Bool                       -- true, false
  | PBin  !PrimOp                      -- +,-,==,<=,...
  deriving (Eq, Ord, Show)

---------------------------------------------------------------------------------
-- | Terms ----------------------------------------------------------------------
---------------------------------------------------------------------------------

-- | Bindings -------------------------------------------------------------------

data Bind a
  = Bind !F.Symbol a
  deriving (Eq, Ord, Show, Functor)

bindId :: Bind a -> F.Symbol
bindId (Bind x _) = x



-- | "Immediate" terms (can appear as function args & in refinements) -----------

data Imm a
  = EVar !F.Symbol a
  | ECon !Prim     a
  deriving (Show, Functor)

-- | Variable definition ---------------------------------------------------------

data Decl a
  = Decl  (Bind a) (Expr a)   a             -- plain      "let"
  | RDecl (Bind a) (Expr a)   a             -- recursive "let rec"
  deriving (Show, Functor)

-- | Terms -----------------------------------------------------------------------

data Expr a
  = EImm !(Imm  a)                     a    -- x,y,z,... 1,2,3...
  | EFun !(Bind a) !(Expr a)           a    -- \x -> e
  | EApp !(Expr a) !(Imm  a)           a    -- e v
  | ELet !(Decl a) !(Expr a)           a    -- let/rec x = e1 in e2
  | EAnn !(Expr a) !RType              a    -- e:t
  | EIf  !(Imm  a) !(Expr a) !(Expr a) a    -- if v e1 e2
  deriving (Show, Functor)

instance Label Imm  where
  label (EVar _ l) = l
  label (ECon _ l) = l

instance Label Expr where
  label (EImm _     l) = l
  label (EFun _ _   l) = l
  label (EApp _ _   l) = l
  label (ELet _ _   l) = l
  label (EAnn _ _   l) = l
  label (EIf  _ _ _ l) = l

instance Label Decl where
  label (Decl  _ _ l) = l
  label (RDecl _ _ l) = l

------------------------------------------------------------------------------
declsExpr :: [Decl a] -> Expr a
------------------------------------------------------------------------------
declsExpr [d]    = ELet d (intExpr 0 l)  l where l = label d
declsExpr (d:ds) = ELet d (declsExpr ds) l where l = label d

intExpr :: Integer -> a -> Expr a
intExpr i l = EImm (ECon (PInt i) l) l

boolExpr :: Bool -> a -> Expr a
boolExpr b l = EImm (ECon (PBool b) l) l

------------------------------------------------------------------------------
type SrcImm    = Imm   F.SrcSpan
type SrcBind   = Bind  F.SrcSpan
type SrcDecl   = Decl  F.SrcSpan
type SrcExpr   = Expr  F.SrcSpan

-- | should/need only be defined on "Known" variants. TODO:LIQUID
instance F.Subable Reft where
  syms     (Known v r)  = v : F.syms r
  substa f (Known v r)  = Known (f v) (F.substa f r)
  substf f (Known v r)  = Known v     (F.substf (F.substfExcept f [v]) r)
  subst su (Known v r)  = Known v     (F.subst  (F.substExcept su [v]) r)
  subst1 (Known v r) su = Known v     (F.subst1Except [v] r su)

instance F.Subable r => F.Subable (Type r) where
  -- syms   :: a -> [Symbol]
  syms (TBase _ r) = F.syms r

  -- substa :: (Symbol -> Symbol) -> Type r -> Type r
  substa f (TBase b r)  = TBase b (F.substa f r)
  substa f (TFun x s t) = TFun x  (F.substa f s) (F.substa f t)

  -- substf :: (Symbol -> Expr) -> Type r -> Type r
  substf f (TBase b r)  = TBase b (F.substf f r)
  substf f (TFun x s t) = TFun  x (F.substf f s) (F.substf f t)

  -- subst  :: Subst -> a -> a
  subst f (TBase b r)  = TBase b (F.subst f r)
  subst f (TFun x s t) = TFun  x (F.subst f s) (F.subst f t)

--------------------------------------------------------------------------------
-- | Substitution --------------------------------------------------------------
--------------------------------------------------------------------------------

substImm :: (F.Subable a) => a -> F.Symbol -> Imm b -> a
substImm thing x y = F.subst su thing
  where
    su          = F.mkSubst [(x, immExpr y)]

subst :: (F.Subable a) => a -> F.Symbol -> F.Symbol -> a
subst thing x y = substImm thing x (EVar y ())

immExpr :: Imm b -> F.Expr
immExpr (EVar x _)             = F.expr x
immExpr (ECon (PInt n) _)      = F.expr n
immExpr (ECon (PBool True) _)  = F.PTrue
immExpr (ECon (PBool False) _) = F.PFalse

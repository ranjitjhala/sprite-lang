{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveFunctor     #-}

module Language.Sprite.L1.Types where 

import qualified Language.Fixpoint.Horn.Types  as H
import qualified Language.Fixpoint.Types       as F
import qualified Language.Sprite.Common.UX      as UX
import           Language.Sprite.Common.Misc    
import           Language.Sprite.Common

-- | Basic types --------------------------------------------------------------

data Base = TInt
  deriving (Eq, Ord, Show)

-- | Refined Types ------------------------------------------------------------

data Type r 
  = TBase !Base r                               -- Int{r} 
  | TFun  !F.Symbol !(Type r) !(Type r)         -- x:s -> t 
  deriving (Eq, Ord, Show)

type RType = Type F.Reft

-- | Primitive Constants ------------------------------------------------------

data PrimOp 
  = BPlus 
  | BMinus 
  | BTimes
  | BLt
  | BGt
  | BEq 
  deriving (Eq, Ord, Show)

data Prim 
  = PInt Integer
  | PBin !PrimOp 
  deriving (Eq, Ord, Show)

-- | Terms --------------------------------------------------------------------
data Decl a = Decl (Bind a) (Expr a)  a
  deriving (Show, Functor)

data Bind a 
  = Bind !F.Symbol a
  deriving (Eq, Ord, Show, Functor)

bindId :: Bind a -> F.Symbol 
bindId (Bind x _) = x

data Imm a
  = EVar !F.Symbol a
  | ECon !Prim     a
  deriving (Show, Functor)

data Expr a 
  = EImm !(Imm  a)            a
  | EFun !(Bind a) !(Expr a)  a
  | EApp !(Expr a) !(Imm  a)  a
  | ELet !(Decl a) !(Expr a)  a
  | EAnn !(Expr a) !RType     a
  deriving (Show, Functor)

instance Label Imm  where 
  label (EVar _ l) = l
  label (ECon _ l) = l

instance Label Expr where 
  label (EImm _   l) = l
  label (EFun _ _ l) = l
  label (EApp _ _ l) = l
  label (ELet _ _ l) = l
  label (EAnn _ _ l) = l
 
instance Label Decl where 
  label (Decl _ _ l) = l

------------------------------------------------------------------------------
declsExpr :: [Decl a] -> Expr a
------------------------------------------------------------------------------
declsExpr [d]    = ELet d (intExpr 0 l)  l where l = label d 
declsExpr (d:ds) = ELet d (declsExpr ds) l where l = label d 
declsExpr _      = UX.panic "declsExpr with empty declarations!" UX.junkSpan  
  
intExpr :: Integer -> a -> Expr a 
intExpr i l = EImm (ECon (PInt i) l) l

------------------------------------------------------------------------------
type SrcImm    = Imm  F.SrcSpan
type SrcBind   = Bind F.SrcSpan
type SrcDecl   = Decl F.SrcSpan
type SrcExpr   = Expr F.SrcSpan

instance F.Subable r => F.Subable (Type r) where 
  -- syms   :: a -> [Symbol]                 
  syms (TBase _ r)  = F.syms r
  syms (TFun _ s t) = F.syms s ++ F.syms t

  -- substa :: (Symbol -> Symbol) -> Type r -> Type r 
  substa f (TBase b r)  = TBase b (F.substa f r)
  substa f (TFun x s t) = TFun x  (F.substa f s) (F.substa f t)

  -- substf :: (Symbol -> Expr) -> Type r -> Type r
  substf f (TBase b r)  = TBase b (F.substf f r)
  substf f (TFun x s t) = TFun  x (F.substf f s) (F.substf f t)

  -- subst  :: Subst -> a -> a
  subst f (TBase b r)  = TBase b (F.subst f r)
  subst f (TFun x s t) = TFun  x (F.subst f s) (F.subst f t)



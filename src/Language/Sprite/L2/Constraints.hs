-- | This module has the kit needed to do constraint generation: 
--   namely, @Env@ironments, @SrcCstr@ manipulation, and @subst@itution.

{-# LANGUAGE OverloadedStrings    #-}

module Language.Sprite.L2.Constraints 
  ( -- * Constraints
    cTrue, cAnd, cHead, cAll

    -- * Substitutions
  , subst, substImm

    -- * Conversions
  , immExpr, predRType

    -- * Environments
  , Env, empEnv, getEnv, extEnv, grdSym
  ) where

import qualified Language.Fixpoint.Horn.Types  as H 
import qualified Language.Fixpoint.Types       as F 
import qualified Language.Sprite.Common.UX     as UX
import           Language.Sprite.Common
import           Language.Sprite.L2.Types 

--------------------------------------------------------------------------------
-- | Constraints ---------------------------------------------------------------
--------------------------------------------------------------------------------
cTrue :: SrcCstr 
cTrue = H.CAnd []

cAnd :: SrcCstr -> SrcCstr -> SrcCstr
cAnd c1 c2 = H.CAnd [c1, c2]

cHead :: F.SrcSpan -> F.Expr -> SrcCstr 
cHead l e = H.Head (H.Reft e) (UX.mkError "Subtype error" l) 

cAll :: F.SrcSpan -> F.Symbol -> RType -> SrcCstr -> SrcCstr
cAll _ x t c = case sortPred x t of 
  Just (so, p) -> H.All (H.Bind x so p) c
  _            -> c

sortPred :: F.Symbol -> RType -> Maybe (F.Sort, H.Pred)
sortPred x (TBase b (F.Reft (v, p))) = Just (baseSort b, H.Reft (subst p v x)) 
sortPred x _                         = Nothing

baseSort :: Base -> F.Sort
baseSort TInt  = F.intSort
baseSort TBool = F.boolSort

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

--------------------------------------------------------------------------------
-- | Environments --------------------------------------------------------------
--------------------------------------------------------------------------------

data Env = Env 
  { eBinds :: !(F.SEnv RType) 
  , eSize  :: !Integer
  }

extEnv :: Env -> Bind a -> RType -> Env  
extEnv env bx t = Env 
  { eBinds = F.insertSEnv (bindId bx) t (eBinds env)
  , eSize  = 1 + eSize env
  }

grdSym :: Env -> F.Symbol
grdSym env = F.tempSymbol "grd" (eSize env)

predRType :: F.Pred -> RType 
predRType p = TBase TBool (F.predReft p)

getEnv :: Env -> F.Symbol -> Maybe RType
getEnv env x = F.lookupSEnv x (eBinds env) 

empEnv :: Env 
empEnv = Env F.emptySEnv 0

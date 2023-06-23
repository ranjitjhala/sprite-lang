-- | This module has the kit needed to do constraint generation:
--   namely, @Env@ironments, @SrcCstr@ manipulation, and @subst@itution.

module Language.Sprite.L1.Constraints
  ( -- * Constraints
    module Language.Sprite.Common.Constraints
  , cAll

    -- * Substitutions
  , subst, substImm

    -- * Environments
  , Env, empEnv, getEnv, extEnv
  ) where

import qualified Language.Fixpoint.Horn.Types  as H
import qualified Language.Fixpoint.Types       as F
import           Language.Sprite.Common.UX
import qualified Language.Sprite.Common.Constraints
import           Language.Sprite.Common
import           Language.Sprite.L1.Types
import Language.Sprite.Common.Constraints (cAll')

--------------------------------------------------------------------------------
-- | Constraints ---------------------------------------------------------------
--------------------------------------------------------------------------------
cAll :: F.SrcSpan -> F.Symbol -> RType -> SrcCstr -> SrcCstr
cAll l x t = cAll' l x (sortPred x t)

sortPred :: F.Symbol -> RType -> Maybe (F.Sort, H.Pred)
sortPred x (TBase b (F.Reft (v, p))) = Just (baseSort b, H.Reft (subst p v x))
sortPred x _                         = Nothing

baseSort :: Base -> F.Sort
baseSort TInt  = F.intSort
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
immExpr (EVar x _)         = F.expr x
immExpr (ECon (PInt n) _)  = F.expr n

--------------------------------------------------------------------------------
-- | Environments --------------------------------------------------------------
--------------------------------------------------------------------------------

type Env  = F.SEnv RType

extEnv :: Env -> Bind a -> RType -> Env
extEnv env bx t = F.insertSEnv (bindId bx) t env

getEnv :: Env -> F.Symbol -> Maybe RType
getEnv env x = F.lookupSEnv x env

empEnv :: Env
empEnv = F.emptySEnv

-- | This module has the kit needed to do constraint generation:
--   namely, @Env@ironments, @SrcCstr@ manipulation, and @subst@itution.

{-# LANGUAGE OverloadedStrings    #-}

module Language.Sprite.L4.Constraints
  ( -- * Constraints
    cTrue, cAnd, cHead, cAll

    -- * Substitutions
  , subst, substImm

    -- * Conversions
  , predRType, baseSort

    -- * Environments
  , Env, empEnv, getEnv, extEnv, extEnvTV, grdSym, envSorts

    -- * Constraint Generation Monad
  , CG, run, failWith, freshK

  ) where

import qualified Data.Maybe                    as Mb
import           Control.Monad.State
import           Control.Monad.Except           (throwError)
import qualified Language.Fixpoint.Horn.Types  as H
import qualified Language.Fixpoint.Types       as F
import qualified Language.Sprite.Common.UX     as UX
import           Language.Sprite.Common
import           Language.Sprite.L4.Types

--------------------------------------------------------------------------------
-- | Constraints ---------------------------------------------------------------
--------------------------------------------------------------------------------
cTrue :: SrcCstr
cTrue = H.CAnd []

cAnd :: SrcCstr -> SrcCstr -> SrcCstr
cAnd (H.CAnd []) c           = c
cAnd c           (H.CAnd []) = c
cAnd c1          c2          = H.CAnd [c1, c2]

cHead :: F.SrcSpan -> H.Pred -> SrcCstr
cHead _ (H.PAnd []) = cTrue
cHead _ (H.Reft p)
  | F.isTautoPred p = cTrue
cHead l p           = H.Head p (UX.mkError "Subtype error" l)

cAll :: F.SrcSpan -> F.Symbol -> RType -> SrcCstr -> SrcCstr
cAll l x t c = case sortPred x t of
  Just (so, p) -> H.All (bind l x so p) c
  _            -> c

sortPred :: F.Symbol -> RType -> Maybe (F.Sort, H.Pred)
sortPred x (TBase b (Known v p)) = Just (baseSort b, subst p v x)
sortPred _ _                     = Nothing

baseSort :: Base -> F.Sort
baseSort TInt     = F.intSort
baseSort TBool    = F.boolSort
baseSort (TVar a) = F.FObj (F.symbol a)

--------------------------------------------------------------------------------
-- | Environments --------------------------------------------------------------
--------------------------------------------------------------------------------

data Env = Env
  { eBinds :: !(F.SEnv RType)     -- ^ value binders
  , eSize  :: !Integer            -- ^ number of binders?
  , eTVars :: !(F.SEnv ())        -- ^ type variables
  }

extEnv :: Env -> F.Symbol -> RType -> Env
extEnv env x t
  | x == junkSymbol = env
  | otherwise       = env { eBinds = F.insertSEnv x t (eBinds env)
                          , eSize  = 1 + eSize env
                          }

extEnvTV :: Env -> TVar -> Env
extEnvTV env (TV a) = env { eTVars = F.insertSEnv a () (eTVars env) }

grdSym :: Env -> F.Symbol
grdSym env = F.tempSymbol "grd" (eSize env)

predRType :: F.Pred -> RType
predRType p = TBase TBool (known $ F.predReft p)

getEnv :: Env -> F.Symbol -> Maybe RType
getEnv env x = F.lookupSEnv x (eBinds env)

empEnv :: Env
empEnv = Env F.emptySEnv 0 F.emptySEnv



envSorts :: Env -> [(F.Symbol, F.Sort)]
envSorts env = [ (x, t) | (x, s) <- F.toListSEnv (eBinds env)
                        , (t, _) <- Mb.maybeToList (sortPred x s) ]

-------------------------------------------------------------------------------
-- | CG Monad -----------------------------------------------------------------
-------------------------------------------------------------------------------

type CG a = StateT CGState (Either [UX.UserError]) a

data CGState = CGState
  { cgCount :: !Integer             -- ^ monotonic counter, to get fresh things
  , cgKVars :: ![SrcHVar]           -- ^ list of generated kvars
  }

s0 :: CGState
s0 = CGState 0 []

run :: CG a -> Either [UX.UserError] (a, [SrcHVar])
run act = do
  (x, s) <- runStateT act s0
  return (x, cgKVars s)

failWith :: UX.Text -> F.SrcSpan -> CG a
failWith msg l = throwError [UX.mkError msg l]

freshK :: F.SrcSpan -> Env -> Base -> CG Reft
freshK l g b = do
  v      <- freshValueSym
  k      <- freshKVar l t ts
  return  $ Known v (H.Var k (v:xs))
  where
    t       = baseSort b
    (xs,ts) = unzip (envSorts g)

freshKVar :: F.SrcSpan -> F.Sort -> [F.Sort] -> CG F.Symbol
freshKVar l t ts = do
  k <- F.kv . F.intKvar <$> freshInt
  _ <- addSrcKVar (H.HVar k (t:ts) (UX.mkError "fake" l))
  return   k

addSrcKVar :: SrcHVar -> CG ()
addSrcKVar k = modify $ \s ->  s { cgKVars = k : cgKVars s }

freshValueSym :: CG F.Symbol
freshValueSym = F.vv . Just <$> freshInt

freshInt :: CG Integer
freshInt = do
  s    <- get
  let n = cgCount s
  put s { cgCount = 1 + n}
  return n

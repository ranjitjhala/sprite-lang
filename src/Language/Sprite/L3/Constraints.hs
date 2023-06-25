-- | This module has the kit needed to do constraint generation:
--   namely, @Env@ironments, @SrcCstr@ manipulation, and @subst@itution.

{-# LANGUAGE OverloadedStrings    #-}

module Language.Sprite.L3.Constraints
  ( -- * Constraints
    cAll

    -- * Substitutions
  , subst, substImm

    -- * Conversions
  , predRType, baseSort

    -- * Environments
  , Env, empEnv, getEnv, extEnv, grdSym, envSorts

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
import           Language.Sprite.L3.Types
import Language.Sprite.Common.Constraints

--------------------------------------------------------------------------------
-- | Constraints ---------------------------------------------------------------
--------------------------------------------------------------------------------
cAll :: F.SrcSpan -> F.Symbol -> RType -> SrcCstr -> SrcCstr
cAll l x t = cAll' l x (sortPred x t)

sortPred :: F.Symbol -> RType -> Maybe (F.Sort, H.Pred)
sortPred x (TBase b (Known v p)) = Just (baseSort b, subst p v x)
sortPred _ _                     = Nothing

baseSort :: Base -> F.Sort
baseSort TInt  = F.intSort
baseSort TBool = F.boolSort

--------------------------------------------------------------------------------
-- | Environments --------------------------------------------------------------
--------------------------------------------------------------------------------

data Env = Env
  { eBinds :: !(F.SEnv RType)
  , eSize  :: !Integer
  }

extEnv :: Env -> F.Symbol -> RType -> Env
extEnv env x t
  | x == junkSymbol = env
  | otherwise       = Env { eBinds = F.insertSEnv x t (eBinds env)
                          , eSize  = 1 + eSize env
                          }

grdSym :: Env -> F.Symbol
grdSym env = F.tempSymbol "grd" (eSize env)

predRType :: F.Pred -> RType
predRType p = TBase TBool (known $ F.predReft p)

getEnv :: Env -> F.Symbol -> Maybe RType
getEnv env x = F.lookupSEnv x (eBinds env)

empEnv :: Env
empEnv = Env F.emptySEnv 0

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

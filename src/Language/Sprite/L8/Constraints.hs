-- | This module has the kit needed to do constraint generation:
--   namely, @Env@ironments, @SrcCstr@ manipulation, and @subst@itution.

{-# LANGUAGE OverloadedStrings    #-}

module Language.Sprite.L8.Constraints
  ( -- * Constraints
    cAll, cAllF, cImpl

    -- * Substitutions
  , subst, substImm

    -- * Conversions
  , predRType, rTypeSort

    -- * Environments
  , Env, empEnv, getEnv, extEnv, extEnvs
  , extEnvTV, grdSym, envSorts
  , getInv, getInv'

    -- * Case-Related manipulation
  , unfoldEnv, unfoldEnv'

    -- * Constraint Generation Monad
  , CG, run, failWith, freshK, freshKVar, freshValueSym
  , addReflectVar
  , CGInfo (..)

    -- * well-formedness
  , wfMetric
  ) where

import qualified Data.List                     as L
import qualified Data.Maybe                    as Mb
import           Control.Monad.State
import           Control.Monad.Except           (throwError)
import qualified Language.Fixpoint.Horn.Types  as H
import qualified Language.Fixpoint.Types       as F
import qualified Language.Fixpoint.SortCheck   as F
import qualified Language.Sprite.Common.UX     as UX
import qualified Language.Sprite.Common.Misc   as Misc
import           Language.Sprite.Common ( SrcCstr, SrcHVar )
import           Language.Sprite.L8.Types
import           Language.Sprite.L8.Prims ( prelude )
import Language.Sprite.Common.Constraints

--------------------------------------------------------------------------------
-- | Constraints ---------------------------------------------------------------
--------------------------------------------------------------------------------
{-@ ListNE a = {v:_ | len v > 0} @-}
type ListNE a = [a]

cImpl :: F.SrcSpan -> ListNE (F.Symbol, RSort) -> H.Pred -> H.Pred -> SrcCstr
cImpl l xts p1 p2  = go [ (x, rSortToFSort t) | (x, t) <- xts]
  where
    go [(x,t)]     = H.All (bind l x t p1)     (cHead l p2)
    go ((x,t):xts) = H.All (bind l x t mempty) (go xts)

cAll :: F.SrcSpan -> F.Symbol -> RType -> SrcCstr -> SrcCstr
cAll l x t = cAll' l x (sortPred x t)

-- | @cAllF@ is a variant of @cAll@ used when the binder is a function, e.g. in [Chk-RAbs]
cAllF :: F.SrcSpan -> F.Symbol -> RType -> SrcCstr -> SrcCstr
cAllF l f t = H.All (bind l f (rTypeSort t) mempty)

sortPred :: F.Symbol -> RType -> Maybe (F.Sort, H.Pred)
sortPred x t@(TBase _     (Known v p)) = Just (rTypeSort t, subst p v x)
sortPred x t@(TCon  _ _ _ (Known v p)) = Just (rTypeSort t, subst p v x)
sortPred _ _                           = Nothing

--------------------------------------------------------------------------------
-- | Environments --------------------------------------------------------------
--------------------------------------------------------------------------------

data Env = Env
  { eBinds :: !(F.SEnv RType)     -- ^ value binders
  , eSize  :: !Integer            -- ^ number of binders?
  , eTVars :: !(F.SEnv ())        -- ^ type variables
  , eSorts :: !(F.SEnv F.Sort)    -- ^ sort-environment (for WF checks)
  , eInv   :: !(F.SEnv Reft)      -- ^ (partial) map from tycon to invariant
  }

instance Show Env where
  show = show . F.toListSEnv . eBinds

extEnv :: Env -> F.Symbol -> RType -> Env
extEnv env x t
  | x == junkSymbol = env
  | otherwise       = env { eBinds = F.insertSEnv x t (eBinds env)
                          , eSize  = 1 + eSize env
                          , eSorts = F.insertSEnv x (rTypeSort t) (eSorts env)
                          }

extEnvs :: Env -> [(F.Symbol, RType)] -> Env
extEnvs = L.foldl' (\g (x, t) -> extEnv g x t)

extEnvTV :: Env -> TVar -> Env
extEnvTV env (TV a) = env { eTVars = F.insertSEnv a () (eTVars env) }

grdSym :: Env -> F.Symbol
grdSym env = F.tempSymbol "grd" (eSize env)

predRType :: F.Pred -> RType
predRType p = TBase TBool (known $ F.predReft p)

getEnv :: Env -> F.Symbol -> Maybe RType
getEnv env x = F.lookupSEnv x (eBinds env)

getInv :: Env -> F.Symbol -> F.Sort -> Maybe H.Pred
getInv env x t = case F.unFApp t of
  F.FTC tc : _ -> case F.lookupSEnv (F.symbol tc) (eInv env) of
                    Just (Known v p) -> Just (subst p v x)
                    _                -> Nothing
  _            -> Nothing

getInv' :: Env -> RType -> RType
getInv' env t@(TCon c _ _ _) = case F.lookupSEnv c (eInv env) of
                                 Nothing -> t
                                 Just r  -> strengthenTop t r
getInv' _   t                = t

empEnv :: [(F.Symbol, F.Sort)] -> [SrcData] -> Env
empEnv ms typs = foldr (\(x, t) g -> extEnv g x t) env0 prelSigs
  where
    env0       = Env mempty 0 mempty (F.fromListSEnv ms) (tcInvs typs)
    prelSigs   = prelude ++ concatMap dataSigs typs

tcInvs :: [SrcData] -> F.SEnv Reft
tcInvs tcs = F.fromListSEnv
  [ (dcName d, inv) | d <- tcs, let inv@(Known v p) = dcInv d, p /= mempty ]

dataSigs :: SrcData -> [(F.Symbol, RType)]
dataSigs dc = [(F.symbol b, t) | (b, t) <- dcCtors dc]

envSorts :: Env -> [(F.Symbol, F.Sort)]
envSorts env = [ (x, t) | (x, s) <- F.toListSEnv (eBinds env)
                        , (t, _) <- Mb.maybeToList (sortPred x s) ]

--------------------------------------------------------------------------------
-- | Well-formedness ------------------------------------------------------------
--------------------------------------------------------------------------------
wfExpr :: F.SrcSpan -> Env -> F.Expr -> F.Sort -> Bool
wfExpr sp g e t = F.checkSortExpr sp (eSorts g) e == Just t

wfMetric :: F.SrcSpan -> Env -> Metric -> Bool
wfMetric sp g m = all (\e -> wfExpr sp g e F.FInt) m

--------------------------------------------------------------------------------
-- | Case-Related Environment Manipulation -------------------------------------
--------------------------------------------------------------------------------
unfoldEnv' :: Env -> Ident -> DaCon -> [SrcBind] -> Maybe Env
unfoldEnv' g y c zs = extEnvs g <$> unfoldEnv g y c zs

unfoldEnv :: Env -> Ident -> DaCon -> [SrcBind] -> Maybe [(F.Symbol, RType)]
unfoldEnv g y c zs = unfold g c y >>= extCase y zs

unfold:: Env -> DaCon -> Ident -> Maybe (RType, RType)
unfold g c y = do
  (as, ps, t)         <- bkAlls <$> getEnv g c
  ty@(TCon _ ts rs _) <- getEnv g y
  prs                 <- Misc.safeZip ps rs
  ats                 <- Misc.safeZip as ts
  return               $ (ty, rsubsts prs . tsubsts ats $ t)

extCase :: Ident -> [SrcBind] -> (RType, RType) -> Maybe [(F.Symbol, RType)]
extCase y zs (ty, t) = go [] (F.symbol <$> zs) t
  where
    go acc (z:zs) (TFun x s t) = go ((z, s) : acc) zs (subst t x z)
    go acc []     t            = Just ((y, meet ty t) : acc)
    go _   _      _            = Nothing

meet :: RType -> RType -> RType
meet t1 t2 = case rTypeReft t2 of
               Just r2 -> strengthenTop t1 r2
               Nothing -> t1



-------------------------------------------------------------------------------
-- | CG Monad -----------------------------------------------------------------
-------------------------------------------------------------------------------

type CG a = StateT CGState (Either [UX.UserError]) a

data CGState = CGState
  { cgCount :: !Integer             -- ^ monotonic counter, to get fresh things
  , cgInfo  :: !CGInfo              -- ^ extra bits needed for constraints
  }

data CGInfo = CGInfo
  { cgiKVars  :: [SrcHVar]
  , cgiConsts :: [(F.Symbol, F.Sort)]
  , cgiDefs   :: [F.Equation]
  }

s0 :: CGState
s0 = CGState 0 (CGInfo [] [] [])

run :: CG a -> Either [UX.UserError] (a, CGInfo)
run act = do
  (x, s) <- runStateT act s0
  return (x, cgInfo s)

failWith :: UX.Text -> F.SrcSpan -> CG a
failWith msg l = throwError [UX.mkError msg l]

freshK :: F.SrcSpan -> Env -> F.Sort -> CG Reft
freshK l g t = do
  v      <- freshValueSym
  k      <- freshKVar l (t:ts)
  return  $ Known v (H.Var k (v:xs))
  where
    -- t       = baseSort b
    (xs,ts) = unzip (envSorts g)

freshKVar :: F.SrcSpan -> [F.Sort] -> CG F.Symbol
freshKVar l ts = do
  k <- F.kv . F.intKvar <$> freshInt
  _ <- addSrcKVar (H.HVar k ts (UX.mkError "fake" l))
  return k

addSrcKVar :: SrcHVar -> CG ()
addSrcKVar k = modify $ \s ->
  let cgi = cgInfo s
      kvs = cgiKVars cgi
  in
    s { cgInfo = cgi { cgiKVars = k : kvs } }

freshValueSym :: CG F.Symbol
freshValueSym = F.vv . Just <$> freshInt

freshInt :: CG Integer
freshInt = do
  s    <- get
  let n = cgCount s
  put s { cgCount = 1 + n}
  return n

addReflectVar :: Ident -> RType -> [(F.Symbol, F.Sort)] -> F.Sort -> F.Expr -> CG ()
addReflectVar f t xts ot e = modify $ \s ->
  let cgi  = cgInfo s
      fDef = {- Misc.traceShow "mkEquation" $ -} F.mkEquation f xts e ot
  in
    s { cgInfo = cgi { cgiConsts = (f, rTypeSort t) : cgiConsts cgi
                     , cgiDefs   = fDef : cgiDefs cgi
                     }
      }

-- | This module has the kit needed to do constraint generation: 
--   namely, @Env@ironments, @SrcCstr@ manipulation, and @subst@itution.

{-# LANGUAGE OverloadedStrings    #-}

module Language.Sprite.L5.Constraints 
  ( -- * Constraints
    cTrue, cAnd, cHead, cAll, pAnd

    -- * Substitutions
  , subst, substImm

    -- * Conversions
  , predRType, rTypeSort

    -- * Environments
  , Env, empEnv, getEnv, extEnv, extEnvs
  , extEnvTV, grdSym, envSorts
  
    -- * Case-Related manipulation
  , unfoldEnv, unfoldEnv'

    -- * Constraint Generation Monad
  , CG, run, failWith, freshK 

  ) where

import qualified Data.List                     as L
import qualified Data.Maybe                    as Mb
import           Control.Monad.State
import           Control.Monad.Except           (throwError)
import qualified Language.Fixpoint.Horn.Types  as H 
import qualified Language.Fixpoint.Types       as F 
import qualified Language.Sprite.Common.UX     as UX
import qualified Language.Sprite.Common.Misc   as Misc 
import           Language.Sprite.Common
import           Language.Sprite.L5.Types 
import           Language.Sprite.L5.Prims  

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
cHead _ (H.Reft p) 
  | F.isTautoPred p = cTrue 
cHead l (H.PAnd ps) = case filter (not . pTrivial) ps of 
                        []  -> cTrue
                        [p] -> mkHead l p 
                        qs  -> mkHead l (H.PAnd qs)
cHead l p           = mkHead l p

mkHead :: F.SrcSpan -> H.Pred -> SrcCstr
mkHead l p = case smash p of 
               []  -> cTrue
               [q] -> mk1 l q 
               qs  -> H.CAnd (mk1 l <$> qs)

mk1 :: F.SrcSpan -> H.Pred -> SrcCstr
mk1 l p = H.Head p (UX.mkError "Subtype error" l)

smash :: H.Pred -> [H.Pred]
smash (H.PAnd ps) = concatMap smash ps
smash p           = [p]

cAll :: F.SrcSpan -> F.Symbol -> RType -> SrcCstr -> SrcCstr
cAll _ x t c = case sortPred x t of 
  Just (so, p) -> H.All (H.Bind x so p) c
  _            -> c

pAnd :: [H.Pred] -> H.Pred
pAnd ps = case filter (not . pTrivial) ps of 
            [p] -> p 
            ps' -> H.PAnd ps'

pTrivial :: H.Pred -> Bool
pTrivial (H.PAnd []) = True
pTrivial (H.Reft p)  = F.isTautoPred p 
pTrivial _           = False

sortPred :: F.Symbol -> RType -> Maybe (F.Sort, H.Pred)
sortPred x t@(TBase _   (Known v p)) = Just (rTypeSort t, subst p v x) 
sortPred x t@(TCon  _ _ (Known v p)) = Just (rTypeSort t, subst p v x) 
sortPred _ _                         = Nothing

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

empEnv :: [SrcData] -> Env 
empEnv typs = Env ctorEnv 0 F.emptySEnv
  where 
    ctorEnv = F.fromListSEnv (prelude ++ concatMap dataSigs typs)



dataSigs :: SrcData -> [(F.Symbol, RType)]
dataSigs (Data _ _ ctors) = [(F.symbol b, t) | (b, t) <- ctors]


envSorts :: Env -> [(F.Symbol, F.Sort)]
envSorts env = [ (x, t) | (x, s) <- F.toListSEnv (eBinds env)
                        , (t, _) <- Mb.maybeToList (sortPred x s) ]

--------------------------------------------------------------------------------
-- | Case-Related Environment Manipulation -------------------------------------
--------------------------------------------------------------------------------
unfoldEnv' :: Env -> Ident -> DaCon -> [SrcBind] -> Maybe Env 
unfoldEnv' g y c zs = extEnvs g <$> unfoldEnv g y c zs

unfoldEnv :: Env -> Ident -> DaCon -> [SrcBind] -> Maybe [(F.Symbol, RType)]
unfoldEnv g y c zs = unfold g c y >>= extCase y zs 

unfold:: Env -> DaCon -> Ident -> Maybe (RType, RType)
unfold g c y = do 
  sig              <- getEnv g c
  ty@(TCon _ ts _) <- getEnv g y
  let (as, t)       = bkAll  sig
  ats              <- Misc.safeZip as ts
  return            $ (ty, tsubsts ats t)

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

{- 
extCaseEnv :: Env -> [Bind F.SrcSpan] -> RType -> Maybe Env 
extCaseEnv g (z:zs) (TFun _ s t) = extCaseEnv g' zs t 
  where 
    g'                           = extEnv g (F.symbol z) s
extCaseEnv g []     _          = Just g 
extCaseEnv _ _      _          = Nothing 

-}

 

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

freshK :: F.SrcSpan -> Env -> F.Sort -> CG Reft
freshK l g t = do
  v      <- freshValueSym
  k      <- freshKVar l t ts
  return  $ Known v (H.Var k (v:xs))
  where
    -- t       = baseSort b
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


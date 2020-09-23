{-# LANGUAGE OverloadedStrings    #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances    #-}

module Language.Sprite.L8.Check (vcgen) where

import           Data.Maybe (isJust)
import           Control.Monad                  (void)
import           Control.Monad.Except           (throwError, catchError)
import qualified Data.HashMap.Strict            as M
import           Text.PrettyPrint.HughesPJ (Doc,  (<+>), text ) 
import qualified Language.Fixpoint.Horn.Types   as H 
import qualified Language.Fixpoint.Types        as F 
import qualified Language.Fixpoint.Misc         as Misc 
import qualified Language.Sprite.Common.UX      as UX 
import           Language.Sprite.Common 
import           Language.Sprite.L8.Types 
import           Language.Sprite.L8.Reflect
import Language.Sprite.L8.Prims ( bTrue, constTy )
import           Language.Sprite.L8.Constraints 
import Language.Sprite.L8.Elaborate ( elaborate )
-- import Debug.Trace (trace)

-------------------------------------------------------------------------------
vcgen:: SrcProg -> Either [UX.UserError] SrcQuery
-------------------------------------------------------------------------------
vcgen (Prog qs ms e typs) = do 
  let env  = empEnv ms typs
  let eL   = elaborate env e 
  let ps   = [(pappSym n, pappSort n) | n <- [1..3]]
  let pqs  = pappQual <$> [1..3]
  (cI, _) <- run (H.CAnd <$> mapM (checkData env) typs)
  (c,cgi) <- run (check env eL (bTrue TInt)) 
  let rfls = cgiConsts cgi
  let syms = M.fromList (ps ++ ms ++ rfls)
  let c'   = strengthenInv env c
  let decs = reflectData <$> Misc.traceShow "data-typs" typs
  return   $ mkQuery (qs ++ pqs) (cgiKVars cgi) (cAnd cI c') syms (cgiDefs cgi) decs

mkQuery :: [F.Qualifier] 
        -> [H.Var a] 
        -> H.Cstr a 
        -> M.HashMap F.Symbol F.Sort 
        -> [F.Equation] 
        -> [F.DataDecl] 
        -> H.Query a
mkQuery qs ks c syms defs ddecls = H.Query 
  { H.qQuals = qs
  , H.qVars  = ks 
  , H.qCstr  = c 
  , H.qCon   = syms 
  , H.qDis   = mempty 
  , H.qEqns  = defs
  , H.qMats  = mempty
  , H.qData  = ddecls
  }

-------------------------------------------------------------------------------
-- | Add Inv assumptions for all data-type binders in SrcCstr
-------------------------------------------------------------------------------
simplCstr :: SrcCstr -> SrcCstr
simplCstr = go
  where
    go (H.CAnd cs) = H.CAnd (go <$> cs)
    go (H.All b c) = H.All  (goB b) (go c)
    go c           = c 
    goB (H.Bind x t p) = H.Bind x t p

-- simplPred :: H.Pred -> H.Pred
-- simplPred = go
--   where 
--     go
--     go (H.PAnd []) = H.Reft mempty
--     go (H.PAnd ps) = H.PAnd [ p' | p' <- go <$> ps, p' /= mempty ] 
--     go (H.Reft e)  = undefined
--     go p           = undefined

-- flatAnd :: [H.Pred] -> [H.Pred]
-- flatAnd = concatMap go
--   where
--     go (H.PAnd ps) = flatAnd ps
--     go p           = [p]

strengthenInv :: Env -> SrcCstr -> SrcCstr 
strengthenInv g = go
  where
    go (H.CAnd cs) = H.CAnd (go <$> cs)
    go (H.All b c) = H.All  (strengthenBind g b) (go c)
    go c           = c

strengthenBind :: Env -> H.Bind -> H.Bind
strengthenBind g b@(H.Bind x t p) = case getInv g x t of
  Nothing -> b 
  Just p' -> H.Bind x t (p <> p')


-------------------------------------------------------------------------------
sub :: F.SrcSpan -> RType -> RType -> CG SrcCstr
-------------------------------------------------------------------------------
sub l s t = sub' l s t `catchError` (\es -> throwError (UX.mkError msg l : es)) 
  where 
    msg = text $ "Invalid Subtyping: " ++ show (s, t)

{- | [Sub-Base]  
     
     (v::t) => q[w := v]
     -------------------
     b{v:p} <= b{w:q}
 -} 

sub' :: F.SrcSpan -> RType -> RType -> CG SrcCstr
sub' l s@(TBase b1 (Known v _)) (TBase b2 (Known w q)) 
  | b1 == b2    = return (cAll l v s (cHead l (subst q w v)))
  | otherwise   = failWith ("Invalid Subtyping: " <+> F.pprint (b1, b2)) l

{- | [Sub-Fun]  
     
     (v::t) => q[w := v]
     -------------------
     b{v:p} <: b{w:q}

    s2 <: s1    x2:s2 |- t1[x1:=x2] <: t2 
    -------------------------------------
    x1:s1 -> t1 <: x2:s2 -> t2

 -}
sub' l (TFun x1 s1 t1) (TFun x2 s2 t2) = do 
  cI   <- sub l s2 s1
  cO   <- cAll l x2 s2 <$> sub l t1' t2
  return (cAnd cI cO)
  where 
    t1' = subst t1 x1 x2

{- | [Sub-TCon] 

      G,v:int{p} |- q[w:=v]     G |- si <: ti
      -----------------------------------------
      G |- (C s1...)[v|p] <: (C t1...)[w|q]

 -}

sub' l s@(TCon c1 t1s p1s (Known v _)) (TCon c2 t2s p2s (Known w q)) | c1 == c2 = do 
  let cTop = cAll  l v s (cHead l (subst q w v)) 
  cIns    <- subs  l t1s t2s 
  cARefs  <- subPs l p1s p2s
  return (cAnd cTop (cAnd cIns cARefs)) 

sub' l t1 t2 = failWith ("sub: cannot handle:" <+> UX.tshow (t1, t2)) l

subs :: F.SrcSpan -> [RType] -> [RType] -> CG SrcCstr
subs _ []       []       = return cTrue 
subs l (t1:t1s) (t2:t2s) = cAnd <$> sub l t1 t2 <*> subs l t1s t2s
subs l _        _        = failWith "subs: invalid args" l

subPs :: F.SrcSpan -> [RARef] -> [RARef] -> CG SrcCstr
subPs l (p1:p1s) (p2:p2s) = cAnd (subP l p1 p2) <$> subPs l p1s p2s
subPs l []       []       = pure cTrue
subPs l _        _        = error "subPs: mismatch"


{- | [Sub-ARef]
     
      G; x1:t... |- p1 => p2[x2 := x1]
      ---------------------------------
      G |- \x1:t. p1 <: \x2:t. p2 

 -}
 
subP :: F.SrcSpan -> RARef -> RARef -> SrcCstr
subP l (ARef xts1 (Known _ p1)) (ARef xts2 (Known _ p2)) 
  = cImpl l xts1 p1 (substs p2 su)
  where 
    su = Misc.safeZip "subP" (fst <$> xts2) (fst <$> xts1)

-------------------------------------------------------------------------------
-- | Checking Invariants 
-------------------------------------------------------------------------------
checkData :: Env -> SrcData -> CG SrcCstr
checkData g d = H.CAnd <$> mapM (checkCtor g (dcInv d)) (dcCtors d)

checkCtor :: Env -> Reft -> (SrcBind, RType) -> CG SrcCstr
checkCtor g inv (dc, t) = checkInv (label dc) g inv t 

checkInv :: F.SrcSpan -> Env -> Reft -> RType -> CG SrcCstr
checkInv l g inv = go
  where
    go (TFun x s t) = cAll l x s' <$> go t   where s'       = getInv' g s
    go (TAll a t)   = go t
    go (TRAll r t)  = cAllF l kf kt <$> go t where (kf, kt) = predBind r
    go t            = sub l t t'             where t'       = tTrue t `strengthenTop` inv

tTrue :: RType -> RType
tTrue = go
  where
    go (TBase b _)      = TBase b mempty
    go (TFun  b s t)    = TFun  b (go s) (go t)
    go (TCon c ts ps _) = TCon  c (go <$> ts) (goP <$> ps) mempty
    go (TAll a t)       = TAll  a (go t)
    go (TRAll a t)      = TRAll a (go t)
    goP (ARef xts _)    = ARef xts mempty

-------------------------------------------------------------------------------
-- | 'Checking' constraints
-------------------------------------------------------------------------------
check :: Env -> SrcExpr -> RType -> CG SrcCstr
-------------------------------------------------------------------------------
{- [Chk-Lam] 

    G, x:s[y:=x] |- e <== t[y:=x]
    -----------------------------
    G |- \x.e <== y:s -> t

 -}
check g (EFun bx e l) (TFun y s t) = do 
  c     <- check (extEnv g x s') e t'
  return $ cAll l x s c
  where
    x  = bindId bx
    s' = subst s y x 
    t' = subst t y x

{- [Chk-Let] 

    G |- e ==> s        G, x:s |- e' <== t'
    -------------------------------------------
        G |- let x = e in e' <== t'

-}
check g (ELet (Let (Bind x l) e _) e' _) t' = do 
  (c, s) <- synth g e
  c'     <- check (extEnv g x s) e' t'
  return  $ cAnd c (cAll l x s c')

{- [Chk-Refl] 
   
   t := fresh(G, s) == forall a*. (y:s)* -> tb      e == \a*.\y*. eb
   G' = G,a*,(y:s)*, x:lim(G, m, t) |- eb <== tb    G, x:reflect(e,t) |- e' <= t'
                                                         ^^^^^^^^^^^^                                                          
  -------------------------------------------------------------------------------
   G |- def x = e:s/m in e' <= t'

 -}

{- [Chk-Rec] 

   t := fresh(G, s) == forall a*. (y:s)* -> tb      e == \a*.\y*. eb
   G' = G,a*,(y:s)*, x:lim(G, m, t) |- eb <== tb    G, x:t |- e' <= t'
   -------------------------------------------------------------------
   G |- let rec x = (e : s / m) in e' <= t' 

 -}
check g (ELet (Rec (Bind x l) (EAnn e ann (_, s, mMb) _) sp) e' _) t' = do
  m               <- fromMaybeM l "Missing termination metric!" mMb
  let (s', m')     = renameTy e s m
  t               <- fresh l g s'
  let (bs, tb, eb) = introEnv t e
  let g'           = foldr (\(x, s) g -> extEnv g x s) g bs
  let tlim         = limit sp g m' t
  c               <- check (extEnv g' x tlim) eb tb
  tx              <- case ann of
                       Val  -> pure t
                       Refl -> reflect x e t
  c'              <- check (extEnv g  x tx) e' t' 
  return           $ cAnd (cAlls l bs c) c'

{- [Chk-If]
   G            |- v  <== bool    
   G, _:{v}     |- e1 <== t      
   G, _:{not v} |- e2 <== t
   ----------------------------- [Chk-If]
   G |- if v e1 e2 <== t
 -}
check g (EIf v e1 e2 l) t = do 
  _  <- check g (EImm v l) rBool 
  c1 <- cAll l xv tT <$> check g e1 t
  c2 <- cAll l xv tF <$> check g e2 t 
  return (cAnd c1 c2) 
  where 
    tT = predRType pv
    tF = predRType (F.PNot pv)
    pv = immExpr v
    xv = grdSym  g

{- [Chk-Switch]

   G | y |- a_i <== t
   ---------------------------
   G |- switch y {a_1...} <== t
-}

check g (ECase y alts _) t = do 
  H.CAnd <$> mapM (checkAlt g y t) alts


{- [Chk-TLam]

  G, a |- e <== t
  ------------------------ [Chk-TLam]
  G |- Λ a. e <== all a. t
-}
check g (ETLam a e _) (TAll b t) | a == b = do
  check g e t

{- [Chk-RAbs]

    ρ = κ:t -> Bool   s' = s[κ := fκ]   G; fκ : t → Bool ⊢ e <== s' 
    ----------------------------------------------------------------[Chk-RAbs]
              G |- e <== all ρ. s

-}
check g e (TRAll r s) = do 
  c <- check g' e s'
  return (cAllF l kf kt c)
  where 
    l        = label e
    g'       = extEnv g kf kt 
    s'       = hvarPred kf <$> s 
    (kf, kt) = predBind r

{- [Chk-Syn]

    G |- e ==> s        G |- s <: t
    ----------------------------------[Chk-Syn]
              G |- e <== t

-}
check g e t = do 
  let l   = label e
  (c, s) <- synth g e
  c'     <- sub l s t
  return    (cAnd c c')

{- [Chk-Syn-Imm] -}
checkImm :: Env -> SrcImm -> RType -> CG SrcCstr
checkImm g i t = do 
  s    <- synthImm g i
  sub (label i) s t



{- [Chk-Alt]

   unfold(G, c, y) === s   G | y + z... * s ~~> G'   G' |- e <== t
   --------------------------------------------------------------- 
   G | y |- C z... -> e <== t

-}
checkAlt :: Env -> Ident -> RType -> SrcAlt -> CG SrcCstr 
checkAlt g y t (Alt c zs e l) = do 
  let al = mconcat (label <$> zs)
  case unfoldEnv g y c zs of 
    Nothing  -> failWith "checkAlt: incompatible pattern" al 
    Just zts -> cAlls l zts <$> check (extEnvs g zts) e t

cAlls :: F.SrcSpan -> [(F.Symbol, RType)] -> SrcCstr -> SrcCstr
cAlls l xts c = foldr (\(x, t) -> cAll l x t) c (reverse xts)

fromMaybeM :: F.SrcSpan -> Doc -> Maybe a -> CG a 
fromMaybeM l msg (Just x) = pure x
fromMaybeM l msg Nothing  = failWith msg l

--------------------------------------------------------------------
-- | 'Synthesis' constraints
--------------------------------------------------------------------
singleton :: F.Symbol -> RType -> RType
singleton x (TBase b      (Known v p)) = TBase b       (Known v (pAnd [p, v `peq` x])) 
singleton x (TCon c ts ps (Known v p)) = TCon  c ts ps (Known v (pAnd [p, v `peq` x])) 
singleton _ t                       = t

peq :: (F.Expression a, F.Expression b) => a -> b -> H.Pred
peq x y = H.Reft (F.PAtom F.Eq (F.expr x) (F.expr y))

synthImm :: Env -> SrcImm -> CG RType
{- [Syn-Var] 
  
   ----------------- 
    G |- x ==> G(x)

-}
synthImm g (EVar x l) 
  | Just t <- getEnv g x = return (singleton x t)
  | otherwise            = failWith ("Unbound variable:" <+> F.pprint x) l

{- [Syn-Con] 

   ----------------- 
    G |- x ==> ty(c)

 -}
synthImm _ (ECon c l) = return (constTy l c)

synth :: Env -> SrcExpr -> CG (SrcCstr, RType)
{- [Syn-Con], [Syn-Var] -}
synth g (EImm i _) = do 
  t <- synthImm g i
  return (cTrue, t)

{- [Syn-Ann]

   G |- e <== t   t := fresh(s)
   ---------------------------
   G |- e:s => t

-}
synth g (EAnn e a (_,s,_) l) = do 
  t <- fresh l g s
  c <- check g e t 
  return (c, t) 


{- [Syn-App]

   G |- e ==> x:s -> t
   G |- y <== s
   -----------------------
   G |- e y ==> t[x := y]

-}
synth g (EApp e y l) = do 
  (ce, te) <- synth g e
  case te of 
    TFun x s t -> do cy <-  checkImm g y s
                     return (cAnd ce cy, substImm t x y)
    _          -> failWith "Application to non-function" l


{- [Syn-TApp]

  G |- e ==> all a. s
  --------------------------- 
  G |- e[t] ==> s [ a := t]

-}
synth g (ETApp e t l) = do 
  (ce, te)   <- synth g e
  case te of
    TAll a s -> do tt <- {- Misc.traceShow "REFRESH" <$> -} refresh l g t 
                   return (ce, {- Misc.traceShow "SYN-TApp: " $ -} tsubst a tt s)
    _        -> failWith "Type Application to non-forall" l 

{- [Syn-RApp] 

   G |- e => forall r.s   r = K:t... -> bool    p = fresh(G, t...-> bool)
   ----------------------------------------------------------------------
   G |- e[?] => s [ r := p ]
 -}

synth g (ERApp e l) = do 
  (c, s) <- synth g e
  s'     <- Misc.traceShow ("SYN-RApp: " ++ show (void e, void s)) <$> rinst l s
  return (c, s')

synth _ e = 
  failWith ("synth: cannot handle: " <+> text (show (void e))) (label e)

-------------------------------------------------------------------------------
-- | Fresh templates for `Unknown` refinements  
-------------------------------------------------------------------------------
refresh :: F.SrcSpan -> Env -> RType -> CG RType 
refresh l g             = fresh l g . go 
  where
    go (TBase b _)      = TBase b Unknown
    go (TFun  b s t)    = TFun  b (go s) (go t)
    go (TCon c ts ps _) = TCon  c (go <$> ts) ps Unknown
    go (TAll a t)       = TAll  a (go t)

fresh :: F.SrcSpan -> Env -> RType -> CG RType 
fresh l g t@(TBase b r)       = TBase b <$> freshR l g (rTypeSort t) r
fresh l g   (TFun  b s t)     = TFun  b <$> fresh  l g s <*> fresh l (extEnv g b s) t
fresh l g t@(TCon  c ts ps r) = TCon  c <$> mapM (fresh l g) ts <*> pure ps <*> freshR l g (rTypeSort t) r
fresh l g   (TAll  a t)       = TAll  a <$> fresh  l g t
fresh l g   (TRAll r t)       = TRAll r <$> fresh  l g t

freshR :: F.SrcSpan -> Env -> F.Sort -> Reft -> CG Reft
freshR _ _ _ r@(Known {}) = pure r
freshR l g t Unknown      = freshK l g t


rinst :: F.SrcSpan -> RType -> CG RType 
rinst l (TRAll (RVar p ts) s) = do 
  ar <- freshKVarReft l ts
  return (subsAR p ar s)
rinst _ s = 
  return s

freshKVarReft :: F.SrcSpan -> [RSort] -> CG RARef
freshKVarReft l ts = do 
  k  <- freshKVar l (rSortToFSort <$> ts)
  return $ rVarARef (RVar k ts) 


---------------------------------------------------------------------------------
-- | Termination: Limiting a Type with a Metric ---------------------------------
---------------------------------------------------------------------------------
limit :: F.SrcSpan -> Env -> Metric -> RType -> RType
limit sp g m t = lim sp g m m t

lim :: F.SrcSpan -> Env -> Metric -> Metric -> RType -> RType
lim sp g mO m (TFun x s t) 
  | isBase s && wfMetric sp (extEnv g x s) mO 
  = TFun x' s' t'
  where
    s'  = (subst s x x') `strengthenTop` (Known x' (H.Reft (wfr mO m')))
    m'  = subst m x x'
    t'  = subst t x x'
    x'  = F.suffixSymbol x "next"

lim sp g mO m (TFun x s t) 
  = TFun x' s' t''
  where
    t'' = lim sp (extEnv g x s) mO m' t'
    m'  = subst m x x'
    s'  = subst s x x'
    t'  = subst t x x'
    x'  = F.suffixSymbol x "next"

lim sp g mO m (TAll a t) 
  = TAll a (lim sp g mO m t)

lim sp g mO m (TRAll a t) 
  = TRAll a (lim sp g mO m t)

lim sp g mO _ t 
  = error $ "Malformed Metric" ++ show (envSorts g, mO, t)

-- Well-foundedness Refinement --------------------------------------------------
wfr :: Metric -> Metric -> F.Expr 
wfr [pO]    [p]   = F.pAnd [nat p, p `lt` pO ]
wfr (pO:mO) (p:m) = F.pAnd [nat p, F.pOr [ p `lt` pO, r ]]
  where
    r             = F.pAnd [p `eq` pO, wfr mO m ] 


-- | Replaces the types in a signature with those in the function definition
renameTy :: SrcExpr -> RType -> Metric -> (RType, Metric)
renameTy (ETLam _ e _) (TAll a t)   m = (TAll a t', m')  
  where 
    (t', m')  = renameTy e t m
renameTy (EFun bx e l) (TFun y s t) m = (TFun x s' t'', m') 
  where
    x          = bindId bx
    s'         = subst s y x 
    t'         = subst t y x
    (t'', m')  = renameTy e t' m
renameTy _ t m = (t, m)

-- | Assumes that the binders in `RType` and `SrcExpr` have been unified   
introEnv :: RType -> SrcExpr -> ([(F.Symbol, RType)] , RType, SrcExpr)
introEnv = go []
  where
    go bs (TFun x s t) (EFun _ e l) = go ((x, s) : bs) t e 
    go bs tb           eb           = (reverse bs, tb, eb)

-- | Abstract Refinement Substitutions (sec 7.2.1) ------------------------------------

{-
rinst :: F.SrcSpan -> RType -> CG RType 
rinst l (TRAll (RVar p ts) s) = do 
  s' <- rinst l s
  k  <- freshKVar l (rSortToFSort <$> ts) 
  return (substKVar p k <$> s') 
rinst _ s = 
  return s 


-- | @substK f k@ replaces all occurences of `H.Var f xs` with `H.Var k xs`
substKVar :: F.Symbol -> F.Symbol -> Reft -> Reft 
substKVar _ _ Unknown     = Unknown
substKVar f k (Known v p) = Known v (go p)
  where 
    go pred = case pred of 
                H.Var g xs | f == g -> H.Var k xs 
                H.PAnd preds        -> H.PAnd (go <$> preds)
                _                   -> pred
-}

-- | @hvarPred f r@ converts all occurrences of `H.Var f xs` in `r` to `H.Reft (EApp f xs)`
hvarPred :: F.Symbol -> Reft -> Reft
hvarPred _ Unknown     = Unknown
hvarPred f (Known v p) = Known v (go p)
  where 
    go (H.Var g xs)
      | f == g         = H.Reft (predApp f xs)
    go (H.PAnd ps)     = H.PAnd (go <$> ps)
    go r               = r

predBind :: RVar -> (F.Symbol, RType)
predBind (RVar p ts) = (p, TCon "Pred" (rSortToRType <$> ts) mempty mempty) 
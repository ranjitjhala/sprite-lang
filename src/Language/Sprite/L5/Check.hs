{-# LANGUAGE OverloadedStrings #-}
module Language.Sprite.L5.Check (vcgen) where

import           Control.Monad                  (void)
import qualified Data.HashMap.Strict            as M
import           Text.PrettyPrint.HughesPJ
import qualified Language.Fixpoint.Horn.Types   as H
import qualified Language.Fixpoint.Types        as F
import qualified Language.Fixpoint.Misc         as Misc
import qualified Language.Sprite.Common.UX      as UX
import           Language.Sprite.Common
import           Language.Sprite.L5.Types
import           Language.Sprite.L5.Prims
import           Language.Sprite.L5.Constraints
import           Language.Sprite.L5.Elaborate
import Language.Sprite.Common.Constraints

-------------------------------------------------------------------------------
vcgen:: SrcProg -> Either [UX.UserError] SrcQuery
-------------------------------------------------------------------------------
vcgen (Prog qs ms e typs) = do
  let env  = empEnv typs
  let eL   = elaborate env ({- trace ("vcgen:" ++ show (void e)) -} e)
  (c, ks) <- run (check env eL (bTrue TInt))
  return   $ H.Query qs ks c (M.fromList ms) mempty mempty mempty mempty

-------------------------------------------------------------------------------
sub :: F.SrcSpan -> RType -> RType -> CG SrcCstr
-------------------------------------------------------------------------------

{- | [Sub-Base]

     (v::t) => q[w := v]
     -------------------
     b{v:p} <= b{w:q}

 -}
sub l s@(TBase b1 (Known v _)) (TBase b2 (Known w q))
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
sub l (TFun x1 s1 t1) (TFun x2 s2 t2) = do
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

sub l s@(TCon c1 t1s (Known v _)) (TCon c2 t2s (Known w q)) | c1 == c2 = do
  let cTop = cAll l v s (cHead l (subst q w v))
  cIns    <- subs l t1s t2s
  return ({- Misc.traceShow "SUB-LIST" $ -} cAnd cTop cIns)

sub l t1 t2 = failWith ("sub: cannot handle:" <+> UX.tshow (t1, t2)) l


subs :: F.SrcSpan -> [RType] -> [RType] -> CG SrcCstr
subs _ []       []       = return cTrue
subs l (t1:t1s) (t2:t2s) = cAnd <$> sub l t1 t2 <*> subs l t1s t2s
subs l _        _        = failWith "subs: invalid args" l

--------------------------------------------------------------------
-- | 'Checking' constraints
--------------------------------------------------------------------
check :: Env -> SrcExpr -> RType -> CG SrcCstr
--------------------------------------------------------------------
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
check g (ELet (Decl (Bind x l) e _) e' _) t' = do
  (c, s) <- synth g e
  c'     <- check (extEnv g x s) e' t'
  return  $ cAnd c (cAll l x s c')

{- [Chk-Rec]

   t := fresh(s)    G; f:t |- e <== t    G; f:t |- e' <== t'
   ---------------------------------------------------------[Chk-Rec]
   G |- letrec f = (e:s) in e' <== t'

 -}
check g (ELet (RDecl (Bind x l) (EAnn e s _) _) e' _) t' = do
  t     <- fresh l g  s
  let g' = extEnv g x t
  c     <- check g' e  t
  c'    <- check g' e' t'
  return $ cAnd c c'

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

-- cAlls l []          c = c
-- cAlls l ((x,t):xts) c = cAll l xts (cAll l x t c)

--------------------------------------------------------------------
-- | 'Synthesis' constraints
--------------------------------------------------------------------
singleton :: F.Symbol -> RType -> RType
singleton x (TBase b   (Known v p)) = TBase b    (Known v (pAnd [p, v `peq` x]))
singleton x (TCon c ts (Known v p)) = TCon  c ts (Known v (pAnd [p, v `peq` x]))
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
synth g (EAnn e s l) = do
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

synth _ e =
  failWith ("synth: cannot handle: " <+> text (show (void e))) (label e)

-------------------------------------------------------------------------------
-- | Fresh templates for `Unknown` refinements
-------------------------------------------------------------------------------
refresh :: F.SrcSpan -> Env -> RType -> CG RType
refresh l g          = fresh l g . go
  where
    go (TBase b _)   = TBase b Unknown
    go (TFun  b s t) = TFun  b (go s) (go t)
    go (TCon c ts _) = TCon  c (go <$> ts) Unknown
    go (TAll a t)    = TAll  a (go t)

fresh :: F.SrcSpan -> Env -> RType -> CG RType
fresh l g t@(TBase b r)    = TBase b <$> freshR l g (rTypeSort t) r
fresh l g   (TFun  b s t)  = TFun  b <$> fresh  l g s <*> fresh l (extEnv g b s) t
fresh l g t@(TCon  c ts r) = TCon  c <$> mapM (fresh l g) ts <*> freshR l g (rTypeSort t) r
fresh l g   (TAll  a t)    = TAll  a <$> fresh  l g t

freshR :: F.SrcSpan -> Env -> F.Sort -> Reft -> CG Reft
freshR _ _ _ r@(Known {}) = pure r
freshR l g t Unknown      = freshK l g t

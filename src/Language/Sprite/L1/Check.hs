{-# LANGUAGE OverloadedStrings #-}
module Language.Sprite.L1.Check (vcgen) where

import           Control.Monad (void)
import qualified Data.Map                       as M
import           Text.PrettyPrint.HughesPJ
import qualified Language.Fixpoint.Horn.Types   as H
import qualified Language.Fixpoint.Types        as F
import qualified Language.Sprite.Common.UX      as UX
import           Language.Sprite.Common
import           Language.Sprite.L1.Types
import           Language.Sprite.L1.Prims
import           Language.Sprite.L1.Constraints
import Language.Sprite.Common.Constraints

-------------------------------------------------------------------------------
vcgen:: SrcExpr -> Either [UX.UserError] SrcQuery
-------------------------------------------------------------------------------
vcgen e = H.Query [] [] <$> check empEnv e (bTrue TInt)
                        <*> pure mempty
                        <*> pure mempty
                        <*> pure mempty
                        <*> pure mempty
                        <*> pure mempty


-- | CG Monad -----------------------------------------------------------------
type CG a = Either [UX.UserError] a

failWith :: UX.Text -> F.SrcSpan -> CG a
failWith msg l = Left [UX.mkError msg l]

-------------------------------------------------------------------------------
sub :: F.SrcSpan -> RType -> RType -> CG SrcCstr
-------------------------------------------------------------------------------

{- | [Sub-Base]

     (v::t) => q[w := v]
     -------------------
     b{v:p} <= b{w:q}

 -}
sub l s@(TBase b1 (F.Reft (v, _))) (TBase b2 (F.Reft (w, q)))
  | b1 == b2    = return (cAll l v s (cHead l (H.Reft (subst q w v))))
  | otherwise   = failWith "Invalid Subtyping" l

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
  cO   <- cAll l x2 t2 <$> sub l t1' t2
  return (cAnd cI cO)
  where
    t1' = subst t1 x1 x2


--------------------------------------------------------------------
-- | 'Checking' constraints
--------------------------------------------------------------------
check :: Env -> SrcExpr -> RType -> CG SrcCstr
--------------------------------------------------------------------


{- [Chk-Lam]

    G, x:s |- e <== t
    --------------------------
    G |- \x.e <== x:s -> t

 -}
check g (EFun bx e l) (TFun y s t) | y == x = do
  c     <- check (extEnv g bx s) e t
  return $ cAll l x s c
  where
    x  = bindId bx

{- [Chk-Let]

    G |- e1 ==> t1        G, x:t1 |- e2 <== t2
    -------------------------------------------
        G |- let x = e1 in e2 <== t2

-}
check g (ELet (Decl bx@(Bind x l) e _) e' _) t' = do
  (c, s) <- synth g e
  c'     <- check (extEnv g bx s) e' t'
  return  $ cAnd c (cAll l x s c')

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


--------------------------------------------------------------------
-- | 'Synthesis' constraints
--------------------------------------------------------------------
synthImm :: Env -> SrcImm -> CG RType

{- [Syn-Var]

   -----------------
    G |- x ==> G(x)

-}
synthImm g (EVar x l)
  | Just t <- getEnv g x = return t
  | otherwise            = failWith ("Unbound variable:" <+> F.pprint x) l

{- [Syn-Con]

   -----------------
    G |- x ==> ty(c)

 -}
synthImm g (ECon c l) = return (constTy l c)


synth :: Env -> SrcExpr -> CG (SrcCstr, RType)
{- [Syn-Con], [Syn-Var] -}
synth g (EImm i _) = do
  t <- synthImm g i
  return (cTrue, t)

{- [Syn-Ann]

   G |- e <== t
   -----------------
   G |- e:t => t

-}
synth g (EAnn e t _) = do
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

synth _ e =
  failWith ("synth: cannot handle: " <+> text (show (void e)  )) (label e)

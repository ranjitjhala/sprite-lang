{-# LANGUAGE OverloadedStrings    #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances    #-}

module Language.Sprite.L8.Reflect (reflectData, reflect) where

import           Control.Monad                  (void)
import qualified Data.HashMap.Strict            as M
import qualified Language.Fixpoint.Horn.Types   as H 
import qualified Language.Fixpoint.Types        as F 
import qualified Language.Fixpoint.Misc         as Misc 
import qualified Language.Sprite.Common.UX      as UX 
import           Language.Sprite.Common         (eq)
import           Language.Sprite.L8.Types 
import           Language.Sprite.L8.Constraints 
-- import Debug.Trace (trace)


---------------------------------------------------------------------------------
reflectData :: SrcData -> F.DataDecl
---------------------------------------------------------------------------------
reflectData (Data tc as _ ctors _) = F.DDecl (fTyCon tc) (length as) fCtors
  where
    tvM    = zipWith (\a i -> (a, F.FVar i)) as [0..]
    fCtors = reflectCtor tvM <$> ctors

type TvSub = [(Ident, F.Sort)] 

reflectCtor :: TvSub -> (SrcBind, RType) -> F.DataCtor
reflectCtor tvM (Bind dc sp, s) = F.DCtor fDc fFields
  where
    fDc       = F.atLoc sp dc
    fFields   = zipWith mkFld fldTs [0..] 
    fldTs     = fmap snd . fsParams . funSig $ s 
    mkFld t i = F.DField (fldName i) (fldSort t)
    fldName i = F.atLoc sp (selDataCon dc i)
    fldSort   = F.sortSubst tvSub . rTypeSort
    tvSub     = F.mkSortSubst tvM

---------------------------------------------------------------------------------
-- | Reflection -----------------------------------------------------------------
---------------------------------------------------------------------------------
reflect :: Ident -> SrcExpr -> RType -> CG RType
reflect f e s = do 
  v <- freshValueSym
  reflectTy f v e s

reflectTy ::  F.Symbol -> F.Symbol -> SrcExpr -> RType -> CG RType
reflectTy f v e0 s0 = go [] e0 s0
  where 
    go xs (ETLam _ e _) (TAll a t)   = do 
      TAll a <$> go xs e t
    go xs (EFun b e _)  (TFun x s t) = do
      let x' = bindId b 
      let s' = subst s x x'
      let t' = subst t x x'
      TFun x' s' <$> go ((x', rTypeSort s') : xs) e t' 
    go xs e t = do 
      let body  = embed e 
      let rbody = Known v (H.Reft (eq v body))
      addReflectVar f s0 (reverse xs) (rTypeSort t) body
      pure (strengthenTop t rbody) 

---------------------------------------------------------------------------------
embed :: SrcExpr -> F.Expr
---------------------------------------------------------------------------------
embed = go
  where 
    go (EImm i _)       = embedImm i
    go e@(EApp {})      = embedApp e
    go (ELet d e _)     = F.subst1 (go e) (goD d) 
    go (EIf i e1 e2 _)  = F.EIte (embedImm i) (go e1) (go e2)
    go (ETLam _ e _)    = go e
    go (ETApp e t _)    = go e -- F.ETApp (go e) (rTypeSort t)
    go (ECase x as _)   = embedAlts x as
    go e                = error ("embed: not handled" ++ show (void e))
    goD (Let b e1 _)    = (bindId b, go e1)

-------------------------------------------------------------------------------
-- | Applications ------------------------------------------------------------- 
-------------------------------------------------------------------------------

embedApp :: SrcExpr -> F.Expr    
embedApp e = case f of
  EImm (ECon (PBin o) _) _ -> embedPrim o         args'
  _                        -> F.eApps   (embed f) args'
  where 
    ((f, _), args) = {- Misc.traceShow "bkApp" $ -} bkApp e
    args'          = embedImm <$> args

bkApp :: SrcExpr -> ((SrcExpr, [RType]), [SrcImm])
bkApp = go []
  where
    go vArgs (EApp f e _)   = go (e:vArgs) f
    go vArgs e              = (goT [] e, vArgs)
    goT tArgs (ETApp f t _) = goT (t:tArgs) f
    goT tArgs e             = (e, tArgs)

-------------------------------------------------------------------------------
-- | Primitives --------------------------------------------------------------- 
-------------------------------------------------------------------------------

embedPrim :: PrimOp -> [F.Expr] -> F.Expr
embedPrim BPlus  [e1, e2] = F.EBin  F.Plus  e1 e2 
embedPrim BMinus [e1, e2] = F.EBin  F.Minus e1 e2 
embedPrim BTimes [e1, e2] = F.EBin  F.Times e1 e2 
embedPrim BLt    [e1, e2] = F.PAtom F.Lt    e1 e2 
embedPrim BLe    [e1, e2] = F.PAtom F.Le    e1 e2
embedPrim BEq    [e1, e2] = F.PAtom F.Eq    e1 e2 
embedPrim BGt    [e1, e2] = F.PAtom F.Gt    e1 e2 
embedPrim BGe    [e1, e2] = F.PAtom F.Ge    e1 e2
embedPrim BAnd   es       = F.PAnd es
embedPrim BOr    es       = F.POr  es 
embedPrim BNot   [e]      = F.PNot e 
embedPrim o      es       = error $ "embedPrim: cannot handle" ++ show (o, es)

embedImm :: SrcImm -> F.Expr
embedImm (EVar x _)         = F.expr x
embedImm (ECon (PInt n) _)  = F.expr n
embedImm (ECon (PBool b) _) = F.expr b
embedImm i                  = error ("embedImm: " ++ show i)

instance F.Expression Bool where 
  expr True  = F.PTrue
  expr False = F.PFalse 

-------------------------------------------------------------------------------
-- | Data types --------------------------------------------------------------- 
-------------------------------------------------------------------------------

embedAlts :: Ident -> [SrcAlt] -> F.Expr
embedAlts x as = go as
  where
    go [a]     = embedAlt x a
    go (a:as)  = F.EIte (isAlt a x) (embedAlt x a) (go as) 

isAlt :: SrcAlt -> Ident -> F.Expr
isAlt a x = mkEApp (isDataCon (altDaCon a)) x

embedAlt :: Ident -> SrcAlt -> F.Expr
embedAlt x a@(Alt d ys e _) = F.subst su (embed e)
  where 
    su      = F.mkSubst $ zipWith sub ys [0..]
    sub y i = (bindId y, mkEApp (selDataCon d i) x)
    yis = zipWith

mkEApp :: F.Symbol -> F.Symbol -> F.Expr
mkEApp f xs = F.eApps (F.expr f) [F.expr xs]

isDataCon :: DaCon -> F.Symbol
isDataCon = F.testSymbol 

selDataCon :: DaCon -> Int -> F.Symbol 
selDataCon d i = F.intSymbol d i


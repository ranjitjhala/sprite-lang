{-# LANGUAGE OverloadedStrings #-}

module Language.Sprite.L8.Prims  where

import qualified Data.Maybe                  as Mb
import qualified Data.Map                    as M
import qualified Language.Fixpoint.Types     as F
import qualified Language.Sprite.Common.UX   as UX
-- import qualified Language.Sprite.Common.Misc as Misc
import           Language.Sprite.L8.Types 
import           Language.Sprite.L8.Parse

-- | "Prelude" Environment --------------------------------------------

prelude :: [(F.Symbol, RType)]
prelude = 
  [ ("diverge"   , mkTy "x:int => 'a")
  , ("impossible", mkTy "x:int[v|false] => 'a")
  , ("Set_empty" , mkTy "x:int => 'a")
  , ("Set_add"   , mkTy "s:Set_Set('a) => x:'a => Set_Set('a)")
  ]

-- | Primitive Types --------------------------------------------------

constTy :: F.SrcSpan -> Prim -> RType
constTy _ (PInt  n)     = TBase TInt  (known $ F.exprReft (F.expr n)) 
constTy _ (PBool True)  = TBase TBool (known $ F.propReft F.PTrue)
constTy _ (PBool False) = TBase TBool (known $ F.propReft F.PFalse)
constTy l (PBin  o)     = binOpTy l o


binOpTy :: F.SrcSpan -> PrimOp -> RType 
binOpTy l o = Mb.fromMaybe err (M.lookup o binOpEnv) 
  where 
    err     = UX.panicS ("Unknown PrimOp: " ++ show o) l

bTrue :: Base -> RType
bTrue b = TBase b mempty



binOpEnv :: M.Map PrimOp RType
binOpEnv = M.fromList 
  [ (BPlus , mkTy "x:int => y:int => int[v|v=x+y]")
  , (BMinus, mkTy "x:int => y:int => int[v|v=x-y]") 
  , (BTimes, mkTy "x:int => y:int => int[v|v=x*y]") 

  , (BLt   , mkTy "x:'a => y:'a => bool[v|v <=> (x <  y)]")
  , (BLe   , mkTy "x:'a => y:'a => bool[v|v <=> (x <= y)]")
  , (BGt   , mkTy "x:'a => y:'a => bool[v|v <=> (x >  y)]")
  , (BGe   , mkTy "x:'a => y:'a => bool[v|v <=> (x >= y)]")
  , (BEq   , mkTy "x:'a => y:'a => bool[v|v <=> (x == y)]")

  , (BAnd  , mkTy "x:bool => y:bool => bool[v|v <=> (x && y)]")
  , (BOr   , mkTy "x:bool => y:bool => bool[v|v <=> (x || y)]")
  , (BNot  , mkTy "x:bool => bool[v|v <=> not x]")
  ]

mkTy :: String -> RType
mkTy = {- Misc.traceShow "mkTy" . -} rebind . generalize . parseWith rtype "prims"  


rebind :: RType -> RType
rebind t@(TBase {})      = t 
rebind (TAll  a t)       = TAll  a (rebind t) 
rebind (TRAll p t)       = TRAll p (rebind t) 
rebind (TCon  c ts ps r) = TCon  c (rebind <$> ts) ps r
rebind (TFun  x s t)     = TFun  x' s' t' 
  where 
    x'                   = F.mappendSym "spec#" x
    s'                   = subst (rebind s) x x'
    t'                   = subst (rebind t) x x'
{-# LANGUAGE OverloadedStrings    #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Language.Sprite.L4.Elaborate (elaborate) where

import qualified Data.Maybe                     as Mb
import qualified Data.List                      as L
import           Control.Exception              (throw)
import           Control.Monad.State
import           Control.Monad.Except           (throwError)
import           Text.PrettyPrint.HughesPJ
--  import           Text.Printf (printf)
import qualified Language.Fixpoint.Types        as F
import           Language.Sprite.Common
-- import qualified Language.Sprite.Common.Misc    as Misc
import qualified Language.Sprite.Common.UX      as UX
import           Language.Sprite.L4.Prims
import           Language.Sprite.L4.Types
import           Language.Sprite.L4.Constraints
import Control.Monad (void)
-- import Debug.Trace (trace)

-------------------------------------------------------------------------------
elaborate   :: SrcExpr -> ElbExpr
-------------------------------------------------------------------------------
elaborate e  = {- trace msg -} e''
  where
    _msg      = "elaborate: " ++ show (void e, void e'')
    e''      = subsTy su e'
    (su, e') = runElabM act
    act      = elabC empEnv e (bTrue TInt)

runElabM :: ElabM a -> (TvSub, a)
runElabM act = case runStateT act s0 of
                 Left errs    -> throw errs
                 Right (v, s) -> (eSub s, v)
  where s0   = ElabS mempty 0

type TvSub   = F.SEnv RType
data ElabS   = ElabS { eSub :: !TvSub, eNum :: !Int }
type ElabM a = StateT ElabS (Either [UX.UserError]) a

unifyV :: F.SrcSpan -> TVar -> RType -> ElabM RType
unifyV _ a t@(TBase (TVar b) r)
  | a == b
  = return t
  | nonRigid a
  = assign a t  >> return t
  | nonRigid b
  = assign b t' >> return t' where t' = TBase (TVar a) r

unifyV l a t
  | a `elem` freeTVars t
  = occurError l a t
  | nonRigid a
  = assign a t  >> return t
  | otherwise
  = rigidError l a t

unify :: F.SrcSpan -> RType -> RType -> ElabM RType
unify l (TBase (TVar a) _) t =
  unifyV l a t
unify l t (TBase (TVar a) _) =
  unifyV l a t
unify _ t1@(TBase b1 _) (TBase b2 _) | b1 == b2 =
  return t1
unify l (TFun x1 s1 t1) (TFun x2 s2 t2) = do
  x   <- pure (unifyX l x1 x2)
  s   <- unify l s1 s2
  t1' <- subsTyM t1
  t2' <- subsTyM t2
  t   <- unify l t1' t2'
  return (TFun x s t)
unify l t1 t2 =
  unifyError l t1 t2

unifyX :: F.SrcSpan -> F.Symbol -> F.Symbol -> F.Symbol
unifyX _ x _ = x

unifyError :: F.SrcSpan -> RType -> RType -> ElabM a
unifyError l t1 t2 = throwError [UX.mkError msg l]
  where msg        = "type error: cannot unify" <+> UX.tshow t1 <+> "and" <+> UX.tshow t2

rigidError :: F.SrcSpan -> TVar -> RType -> ElabM a
rigidError l a t = throwError [UX.mkError msg l]
  where msg      = "type error: cannot assign rigid" <+> UX.tshow a <+> "the type" <+> UX.tshow t

occurError :: F.SrcSpan -> TVar -> RType -> ElabM a
occurError l a t = throwError [UX.mkError msg l]
  where msg      = "type error: occurs check" <+> UX.tshow a <+> "occurs in" <+> UX.tshow t

-------------------------------------------------------------------------------
elabC :: Env -> SrcExpr -> RType -> ElabM ElbExpr
elabC g (EFun b e l) (TFun _ s t) = do
  e'    <- elabC (extEnv g (bindId b) s) e t
  return $ EFun b e' l

-- let rec x:s = e1 in e2
elabC g (ELet (RDecl (Bind x l) (EAnn e1 s1 l1) ld) e2 l2) t2 = do
  let g' = extEnv g x s1
  let (as, t1) = splitTAll s1
  e1'   <- elabC (extEnvTVs g' as) e1 t1
  e2'   <- elabC g' e2 t2
  return $ ELet (RDecl (Bind x l) (EAnn (mkTLam e1' as) s1 l1) ld) e2' l2

-- let x = e in e'
elabC g (ELet (Decl (Bind x l) e1 l1) e2 l2) t2 = do
  (e1', s) <- elabS g e1
  e2'      <- elabC (extEnv g x s) e2 t2
  return    $ ELet (Decl (Bind x l) e1' l1) e2' l2

-- if b e1 e2
elabC g (EIf b e1 e2 l) t = do
  e1'   <- elabC g e1 t
  e2'   <- elabC g e2 t
  return $ EIf b e1' e2' l

elabC g e t = do
  (e', t') <- elabS g e
  unify (label e) t t'
  return e'

immS :: Env -> SrcImm -> ElabM ([RType], RType)
immS g i = instantiate =<< immTy g i

extEnvTVs :: Env -> [TVar] -> Env
extEnvTVs = foldr (flip extEnvTV)

-------------------------------------------------------------------------------
elabS :: Env -> SrcExpr -> ElabM (ElbExpr, RType)
elabS g e@(EImm i _) = do
  (ts, t') <- {- Misc.traceShow ("elabS" ++ show i) <$> -} immS g i
  return (mkTApp e ts, t')

elabS g (EAnn e s l) = do
  let (as, t) = splitTAll s
  e' <- elabC (extEnvTVs g as) e t
  return (EAnn (mkTLam e' as) s l, s)

elabS g (EApp e y l) = do
  (e', te) <- elabS g e
  case te of
    TFun _ s t -> do unify l s =<< immTy g y
                     return (EApp e' y l, t)
    _          -> elabErr "Application to non-function" l

elabS _ e =
    elabErr ("elabS unexpected:" <+> UX.tshow (void e))  (label e)


-------------------------------------------------------------------------------

elabErr :: UX.Text -> F.SrcSpan -> ElabM a
elabErr msg l = throwError [UX.mkError msg l]

instantiate :: RType -> ElabM ([RType], RType)
instantiate = go []
 where
    go ts (TAll a s) = do v      <- fresh
                          let vt  = TBase (TVar v) mempty
                          go (vt:ts) (tsubst a vt s)
    go ts s          = return (reverse ts, s)

splitTAll :: RType -> ([TVar], RType)
splitTAll (TAll a s) = (a:as, t) where (as, t) = splitTAll s
splitTAll t          = ([]  , t)

fresh :: ElabM TVar
fresh = do
  s    <- get
  let n = eNum s
  put s { eNum = n + 1 }
  return (nonRigidTV n)

nonRigidTV :: Int -> TVar
nonRigidTV = TV . F.intSymbol "fv"

nonRigid :: TVar -> Bool
nonRigid (TV a) = F.isPrefixOfSym "fv" a

immTy :: Env -> SrcImm -> ElabM RType
immTy g (EVar x l)
 | Just t <- getEnv g x = return ({- Misc.traceShow ("immTy: " ++ show x) -} t)
 | otherwise            = elabErr ("Unbound variable:" <+> F.pprint x) l
immTy _ (ECon c l)      = return (constTy l c)

mkTLam :: SrcExpr -> [TVar] -> ElbExpr
mkTLam = foldr (\a e -> ETLam a e (label e))

mkTApp :: SrcExpr -> [RType] -> ElbExpr
mkTApp = L.foldl' (\e t -> ETApp e t (label e))

-- | Type Substitutions --------------------------------------------------------------

class SubsTy a where
  subsTy  :: TvSub -> a -> a
  subsTy1 :: TVar -> RType -> a -> a
  subsTy1 a t x = subsTy (singTvSub a t) x

singTvSub :: TVar -> RType -> TvSub
singTvSub a t = F.fromListSEnv [(F.symbol a, t)]

instance SubsTy RType where
  subsTy su t@(TBase (TVar a) _) = Mb.fromMaybe t t'
    where
      t'                         = F.lookupSEnv (F.symbol a) su

  subsTy _su t@(TBase {})        = t

  subsTy su (TFun x s t)         = TFun x s' t'
    where
      s'                         = subsTy su s
      t'                         = subsTy su t

  subsTy su (TAll a t)           = TAll a t'
    where
      t'                         = subsTy su' t
      su'                        = F.deleteSEnv (F.symbol a) su

instance SubsTy TvSub where
  subsTy = F.mapSEnv . subsTy

-- applies the substs to the ETApp types
instance SubsTy ElbExpr where
  subsTy = subsTyExpr

instance SubsTy ElbDecl where
  subsTy su (Decl  b e l) = Decl  b (subsTy su e) l
  subsTy su (RDecl b e l) = RDecl b (subsTy su e) l

subsTyExpr :: TvSub -> ElbExpr -> ElbExpr
subsTyExpr su           = go
  where
    go (EFun b e l)     = EFun  b (go e)               l
    go (EApp e i l)     = EApp    (go e)  i            l
    go (ELet d e l)     = ELet    d'      (go e)       l where d' = subsTy su d
    go (EAnn e t l)     = EAnn    (go e)  t            l
    go (EIf  i e1 e2 l) = EIf   i (go e1) (go e2)      l
    go (ETLam a e l)    = ETLam a (go e)               l
    go (ETApp e t l)    = ETApp   (go e) (subsTy su t) l
    go e@(EImm {})      = e





subsTyM :: (SubsTy a) => a -> ElabM a
subsTyM x = do
  su <- gets eSub
  return (subsTy su x)

assign :: TVar -> RType -> ElabM ()
assign a t = modify $ \s -> s { eSub = updSub a t (eSub s)}

updSub :: TVar -> RType -> TvSub -> TvSub
updSub a t su = F.insertSEnv (F.symbol a) t (subsTy1 a t su)

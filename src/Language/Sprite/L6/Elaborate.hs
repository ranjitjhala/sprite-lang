{-# LANGUAGE OverloadedStrings    #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Language.Sprite.L6.Elaborate (elaborate) where

import qualified Data.Maybe                     as Mb
import qualified Data.List                      as L
import           Control.Exception              (throw)
import           Control.Monad.State
import           Control.Monad.Except           (throwError)
import           Text.PrettyPrint.HughesPJ
--  import           Text.Printf (printf)
import qualified Language.Fixpoint.Types        as F
import           Language.Sprite.Common
import qualified Language.Sprite.Common.Misc    as Misc
import qualified Language.Sprite.Common.UX      as UX
import           Language.Sprite.L6.Prims
import           Language.Sprite.L6.Types
import           Language.Sprite.L6.Constraints
import Debug.Trace (trace)
import Control.Monad (void)

-------------------------------------------------------------------------------
elaborate   :: Env -> SrcExpr -> ElbExpr
-------------------------------------------------------------------------------
elaborate g e = {- trace _msg -} e''
  where
    _msg      = "elaborate: " ++ show (F.toListSEnv su, void e, void e'')
    e''       = subsTy su e'
    (su, e')  = runElabM act
    act       = elabC g e (bTrue TInt)

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
unify l (TCon c1 t1s _ _) (TCon c2 t2s _ _) | c1 == c2 = do
  ts <- unifys l t1s t2s
  return (TCon c1 ts mempty mempty)

unify l t1 t2 =
  unifyError l t1 t2

unifys :: F.SrcSpan -> [RType] -> [RType] -> ElabM [RType]
unifys _ []       []       =
  return []
unifys l (t1:t1s) (t2:t2s) = do
  t    <- unify l t1 t2
  t1s' <- mapM subsTyM t1s
  t2s' <- mapM subsTyM t2s
  ts   <- unifys l t1s' t2s'
  return (t:ts)
unifys l _ _               =
  throwError [UX.mkError "unifys-mismatched args" l]


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

matchError :: F.SrcSpan -> Doc -> ElabM a
matchError l msg = throwError [UX.mkError ("case-alt error:" <+> msg) l]

-------------------------------------------------------------------------------
elabC :: Env -> SrcExpr -> RType -> ElabM ElbExpr
elabC g (EFun b e l) (TFun _ s t) = do
  e'    <- elabC (extEnv g (bindId b) s) e t
  return $ EFun b e' l

-- let rec x:s = e1 in e2
elabC g (ELet (RDecl (Bind x l) (EAnn e1 s1 l1) ld) e2 l2) t2 = do
  let g'          = extEnv g x s1
  let (as, _, t1) = bkAlls s1
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

-- switch (y) {  | C(z..) => e | ... }
elabC g (ECase y alts l) t = do
  alts' <- mapM (elabAlt g y t) alts
  return $ ECase y alts' l

elabC g e t = do
  (e', t') <- elabS g e
  unify (label e) t t'
  return e'

elabAlt :: Env -> Ident -> RType -> SrcAlt -> ElabM SrcAlt
elabAlt g y t (Alt c zs e l) = do
  let al = mconcat (label <$> zs)
  case unfoldEnv' g y c zs of
    Nothing -> matchError al "bad pattern match"
    Just g' -> (\e' -> Alt c zs e' l) <$> elabC g' e t



extEnvTVs :: Env -> [TVar] -> Env
extEnvTVs = foldr (flip extEnvTV)

-------------------------------------------------------------------------------
elabS :: Env -> SrcExpr -> ElabM (ElbExpr, RType)
elabS g e@(EImm i _) = do
  (ts, n, t') <- Misc.traceShow ("elabS: " ++ show i) <$> immS g i
  return (mkTApp e ts n, t')

elabS g (EAnn e s l) = do
  let (as, _, t) = bkAlls s
  e' <- elabC (extEnvTVs g as) e t
  return (EAnn (mkTLam e' as) s l, s)

elabS g (EApp e y l) = do
  (e', te) <- elabS g e
  case te of
    TFun _ s t -> do (\(_,_,yt) -> unify l s ({- Misc.traceShow ("elabS1 " ++ show s) -} yt) ) =<< immS g y
                     t' <- subsTyM t
                     return (EApp e' y l, t')
    _          -> elabErr ("elabS: Application to non-function; caller type = " <+> UX.tshow te)  l

elabS _ e =
    elabErr ("elabS unexpected:" <+> UX.tshow (void e))  (label e)


-------------------------------------------------------------------------------

elabErr :: UX.Text -> F.SrcSpan -> ElabM a
elabErr msg l = throwError [UX.mkError msg l]

instantiate :: RType -> ElabM ([RType], Int, RType)
instantiate = go [] 0
 where
    go ts n (TAll a s)  = do v      <- fresh
                             let vt  = TBase (TVar v) mempty
                             go (vt:ts) n (tsubst a vt s)
    go ts n (TRAll _ s) = go ts (n+1) s
    go ts n s           = return (reverse ts, n, s)

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

immS :: Env -> SrcImm -> ElabM ([RType], Int, RType)
immS g i = instantiate =<< immTy g i
  where
    immTy :: Env -> SrcImm -> ElabM RType
    immTy g (EVar x l)
      | Just t <- getEnv g x = return t
      | otherwise            = elabErr ("Unbound variable:" <+> F.pprint x) l
    immTy _ (ECon c l)       = return (constTy l c)

mkTLam :: SrcExpr -> [TVar] -> ElbExpr
mkTLam = foldr (\a e -> ETLam a e (label e))

mkTApp :: SrcExpr -> [RType] -> Int -> ElbExpr
mkTApp e ts n   = mkRApps n (mkTApps e ts)
  where
    mkRApps 0 e = e
    mkRApps k e = mkRApps (k-1) (ERApp e (label e))
    mkTApps     = L.foldl' (\e t -> ETApp e t (label e))

-- | Type Substitutions --------------------------------------------------------------

class SubsTy a where
  subsTy  :: TvSub -> a -> a
  subsTy1 :: TVar -> RType -> a -> a
  subsTy1 a t x = subsTy (singTvSub a t) x

singTvSub :: TVar -> RType -> TvSub
singTvSub a t = F.fromListSEnv [(F.symbol a, t)]

instance SubsTy RARef where
  subsTy su (ARef xts p) = ARef xts' p
    where
      xts'               = [(x, subsTy su t) | (x, t) <- xts ]

instance SubsTy RType where
  subsTy su t@(TBase (TVar a) _) = Mb.fromMaybe t t'
    where
      t'                         = F.lookupSEnv (F.symbol a) su

  subsTy _su t@(TBase {})        = t

  subsTy su (TCon c ts ps r)        = TCon c (subsTy su <$> ts) (subsTy su <$> ps) r

  subsTy su (TFun x s t)         = TFun x s' t'
    where
      s'                         = subsTy su s
      t'                         = subsTy su t

  subsTy su (TAll a t)           = TAll a t'
    where
      t'                         = subsTy su' t
      su'                        = F.deleteSEnv (F.symbol a) su

  subsTy su (TRAll p t)          = TRAll p' t'
    where
      t'                         = subsTy su t
      p'                         = subsTy su p

instance SubsTy RVar where
  subsTy su (RVar p args)        = RVar p (subsTy su <$> args)

instance SubsTy RSort where
  subsTy su                      = asRType (subsTy su)

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
    go (ERApp e   l)    = ERApp   (go e)               l
    go (ECase x as l)   = ECase x (goA <$> as)         l
    go e@(EImm {})      = e
    goA alt             = alt -- { altTyArgs = fmap (subsTy su) <$> altTyArgs alt }
                              { altExpr = go $  altExpr   alt }




subsTyM :: (SubsTy a) => a -> ElabM a
subsTyM x = do
  su <- gets eSub
  return (subsTy su x)

assign :: TVar -> RType -> ElabM ()
assign a t = modify $ \s -> s { eSub = updSub a t (eSub s)}

updSub :: TVar -> RType -> TvSub -> TvSub
updSub a t su = F.insertSEnv (F.symbol a) t (subsTy1 a t su)

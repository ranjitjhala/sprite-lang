-- | This module has some code for building Horn constraints that is common to all languages

{-# LANGUAGE OverloadedStrings    #-}

module Language.Sprite.Common.Constraints
  (
  -- * Symbols
    anon, isAnon,

    -- * Constraints
    cTrue, cAnd, cHead, cAll', pAnd, bind
  ) where

import qualified Language.Fixpoint.Horn.Types  as H
import qualified Language.Fixpoint.Types       as F
import qualified Language.Sprite.Common.UX     as UX
import           Language.Sprite.Common

--------------------------------------------------------------------------------
-- | Symbols -------------------------------------------------------------------
--------------------------------------------------------------------------------
anonSymbol :: F.Symbol
anonSymbol = "anon"

anon :: Integer -> F.Symbol
anon = F.tempSymbol anonSymbol

isAnon :: F.Symbol -> Bool
isAnon = F.isPrefixOfSym anonSymbol

--------------------------------------------------------------------------------
-- | Constraints ---------------------------------------------------------------
--------------------------------------------------------------------------------
cTrue :: SrcCstr
cTrue = H.CAnd []

cAnd :: SrcCstr -> SrcCstr -> SrcCstr
cAnd (H.CAnd []) c           = c
cAnd c           (H.CAnd []) = c
cAnd (H.CAnd cs) (H.CAnd ds) = H.CAnd (cs ++ ds)
cAnd (H.CAnd cs) d           = H.CAnd (cs ++ [d])
cAnd d           (H.CAnd cs) = H.CAnd (d : cs)
cAnd c1          c2          = H.CAnd [c1, c2]


pAnd :: [H.Pred] -> H.Pred
pAnd ps = case filter (not . pTrivial) ps of
            [p] -> p
            ps' -> H.PAnd ps'

-- cHead :: F.SrcSpan -> F.Expr -> SrcCstr
-- cHead l e = H.Head (H.Reft e) (UX.mkError "Subtype error" l)

cHead :: F.SrcSpan -> H.Pred -> SrcCstr
cHead _ (H.Reft p)
  | F.isTautoPred p = cTrue
cHead l (H.PAnd ps) = case filter (not . pTrivial) ps of
                        []  -> cTrue
                        [p] -> mkHead l p
                        qs  -> mkHead l (H.PAnd qs)
cHead l p           = mkHead l p

pTrivial :: H.Pred -> Bool
pTrivial (H.PAnd []) = True
pTrivial (H.Reft p)  = F.isTautoPred p
pTrivial _           = False


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

cAll' :: F.SrcSpan -> F.Symbol -> Maybe (F.Sort, H.Pred) -> SrcCstr -> SrcCstr
cAll' l x sp c = case sp of
  Just (so, p) -> H.All (bind l x so p) c
  _            -> c

bind :: F.SrcSpan -> F.Symbol -> F.Sort -> H.Pred -> H.Bind UX.UserError
bind l x so p = H.Bind x so p (UX.mkError "head" l)

-- cAll :: F.SrcSpan -> F.Symbol -> RType -> SrcCstr -> SrcCstr
-- cAll l x t c = case sortPred x t of
--   Just (so, p) -> H.All (H.Bind x so p tag) c where tag = UX.mkError "head" l
--   _            -> c

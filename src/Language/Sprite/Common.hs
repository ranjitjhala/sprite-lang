
{-# LANGUAGE OverloadedStrings    #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Eta reduce" #-}

-- | Some types that are common to all languages -------------------------------

module Language.Sprite.Common where

import           System.Exit ( ExitCode, exitWith )
import           Control.Exception ( catch )
import           Control.Monad (when)
import qualified Data.Maybe as Mb
import qualified Text.PrettyPrint.HughesPJ      as PJ
import qualified Language.Fixpoint.Horn.Types   as H
import qualified Language.Fixpoint.Horn.Solve   as H
import qualified Language.Fixpoint.Types.Config as FC
import qualified Language.Fixpoint.Types.Errors as F
import qualified Language.Fixpoint.Types        as F
import qualified Language.Fixpoint.Misc         as F
import qualified Language.Fixpoint.Utils.Files  as F
import qualified Language.Sprite.Common.UX      as UX

type SrcCstr   = H.Cstr      UX.UserError
type SrcQuery  = H.Query     UX.UserError
type SrcResult = F.FixResult UX.UserError
type SrcHVar   = H.Var       UX.UserError

---------------------------------------------------------------------------
query :: [F.Qualifier] -> [H.Var a] -> H.Cstr a -> H.Query a
---------------------------------------------------------------------------
query qs ks c = H.Query qs ks c mempty mempty mempty mempty mempty mempty

---------------------------------------------------------------------------
bind :: F.SrcSpan -> F.Symbol -> F.Sort -> H.Pred -> H.Bind UX.UserError
---------------------------------------------------------------------------
bind sp x t p = H.Bind x t p (UX.mkError mempty sp)

---------------------------------------------------------------------------
crash :: [UX.UserError] -> String -> SrcResult
---------------------------------------------------------------------------
crash errs = F.Crash [(e, Nothing) | e <- errs]



class Label t where
  label :: t a -> a


---------------------------------------------------------------------------
doOrDie :: IO a -> IO a
---------------------------------------------------------------------------
doOrDie act = act `catch` crashFPError   "Parse error"
                  `catch` crashUserError "Unexpected error"

crashFPError :: String -> F.Error -> IO a
crashFPError msg ferr = crashUserError msg (UX.fpUserError <$> F.errs (F.traceShow "WTF" ferr))

crashUserError :: String -> [UX.UserError] -> IO a
crashUserError msg es = exitWith =<< resultExit (F.Crash [(e, Nothing) | e <- es] msg)

---------------------------------------------------------------------------
checkValid :: FilePath -> SrcQuery -> IO SrcResult
---------------------------------------------------------------------------
checkValid f = checkValidWithCfg f fpConfig

---------------------------------------------------------------------------
checkValidPLE :: FilePath -> SrcQuery -> IO SrcResult
---------------------------------------------------------------------------
checkValidPLE f q = do
  pleCfg <- FC.withPragmas fpConfig ["--rewrite"]
  checkValidWithCfg f pleCfg q

checkValidWithCfg :: FilePath -> FC.Config -> SrcQuery -> IO SrcResult
checkValidWithCfg f cfg q = do
  dumpQuery f q
  fmap snd . F.resStatus <$> H.solve cfg q

fpConfig :: FC.Config
fpConfig = FC.defConfig
  { FC.eliminate = FC.Some }

dumpQuery :: FilePath -> SrcQuery -> IO ()
dumpQuery f q = when True $ do
  putStrLn (F.wrapStars "BEGIN: Horn VC")
  let smtFile = F.extFileName F.Smt2 f
  F.ensurePath smtFile
  writeFile smtFile (PJ.render . F.pprint $ q)
  putStrLn (F.wrapStars "END: Horn VC")

---------------------------------------------------------------------------
resultExit :: SrcResult -> IO ExitCode
---------------------------------------------------------------------------
resultExit r = do
  F.colorStrLn (F.colorResult r) (resultStr r)
  case resultErrs r of
    [] -> return ()
    es -> putStrLn . PJ.render =<< UX.renderErrors es
  return (F.resultExit r)

resultErrs :: SrcResult -> [UX.UserError]
resultErrs (F.Unsafe _ es) = es
resultErrs (F.Crash es _)  = fst <$> es
resultErrs _               = []

resultStr :: SrcResult -> String
resultStr (F.Safe {})     = "Safe"
resultStr (F.Unsafe {})   = "Unsafe"
resultStr (F.Crash _ msg) = "Crash!: " ++ msg

---------------------------------------------------------------------------------
nat :: F.Expr -> F.Expr
nat p = F.PAtom F.Le (F.ECon (F.I 0)) p

lt :: F.Expr -> F.Expr -> F.Expr
lt e1 e2 = F.PAtom F.Lt e1 e2

eq :: (F.Expression a, F.Expression b) => a -> b -> F.Expr
eq e1 e2 = F.PAtom F.Eq (F.expr e1) (F.expr e2)

---------------------------------------------------------------------------------

-- predApp f xs = F.eApps (F.expr f) (F.expr <$> xs)

predApp :: (F.Expression e) => F.Symbol -> [e] -> F.Expr
predApp f xs = F.eApps (F.expr pn) (F.expr f : (F.expr <$> xs))
  where
    pn       = pappSym n
    n        = length xs

pappSym :: Int -> F.Symbol
pappSym n  = F.symbol $ "papp" ++ show n

pappSortArgs :: Int -> [F.Sort] -> F.Sort
pappSortArgs tvars args = F.mkFFunc tvars $ ptycon : args ++ [F.boolSort]
  where
    ptycon              = F.fAppTC predFTyCon args

pappSort :: Int -> F.Sort
pappSort n = pappSortArgs n (pappArgs n)

pappArgs :: Int -> [F.Sort]
pappArgs n = F.FVar <$> [0 .. n-1]

pappQual :: Int -> F.Qualifier
pappQual n = F.mkQ name (vt : args ++ [(p, pt)]) pred pos
  where
    pt     = F.fAppTC predFTyCon (snd <$> args ++ [vt])
    name   = F.symbol ("PApp" ++ show n)
    vt     = (F.vv Nothing, F.FVar (n-1))
    args   = [ (x i, F.FVar i) | i <- [0 .. n-2] ]
    p      = "p"
    x i    = F.symbol ("x" ++ show i)
    pred   = predApp p (fst <$> (args ++ [vt]))
    pos    = F.dummyPos "pappQual"

predFTyCon :: F.FTycon
predFTyCon = F.symbolFTycon (F.dummyLoc "Pred")

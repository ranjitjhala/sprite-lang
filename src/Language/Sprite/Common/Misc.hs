module Language.Sprite.Common.Misc where

import qualified Data.Map  as M
import qualified Data.List as L
-- import           Data.Monoid
import           Data.Maybe (fromMaybe)
import           Data.Char (isSpace)
import           Control.Exception
import           Control.Monad
import           Text.Printf
import           System.Directory
import           System.Exit
import           System.FilePath
import           System.IO
import           System.Process
import           System.Timeout
import           System.Console.CmdArgs.Verbosity (whenLoud)
import           Debug.Trace (trace)

safeZip :: [a] -> [b] -> Maybe [(a, b)]
safeZip xs ys
  | length xs == length ys = Just (zip xs ys)
  | otherwise              = Nothing

--------------------------------------------------------------------------------
(>->) :: (a -> Either e b) -> (b -> c) -> a -> Either e c
--------------------------------------------------------------------------------
f >-> g = f >=> safe g
  where
    safe :: (a -> b) -> a -> Either c b
    safe h x = Right (h x)

groupBy :: (Ord k) => (a -> k) -> [a] -> [(k, [a])]
groupBy f = M.toList . L.foldl' (\m x -> inserts (f x) x m) M.empty

inserts :: (Ord k) => k -> v -> M.Map k [v] -> M.Map k [v]
inserts k v m = M.insert k (v : M.findWithDefault [] k m) m

mapSnd :: (b -> c) -> (a, b) -> (a, c)
mapSnd f (x, y) = (x, f y)

-- >>> dupBy fst [(1, "one"), (2, "two"), (3, "three"), (1, "uno")]
-- [[(1,"uno"),(1,"one")]]
--
-- >>> dupBy fst [(1, "one"), (2, "two"), (3, "three")]
-- []

dupBy :: (Ord k) => (a -> k) -> [a] -> [[a]]
dupBy f xs = [ xs' | (_, xs') <- groupBy f xs, 2 <= length xs' ]

trim :: String -> String
trim = f . f  where f = reverse . dropWhile isSpace

trimEnd :: String -> String
trimEnd = reverse . dropWhile isSpace . reverse

executeShellCommand :: FilePath -> String -> Int -> IO ExitCode
executeShellCommand logF cmd n = fromMaybe (ExitFailure 100) <$> body
  where
    body = timeout n . withFile logF AppendMode $ \h -> do
             let p       = (shell cmd) {std_out = UseHandle h, std_err = UseHandle h}
             (_,_,_,ph) <- createProcess p
             waitForProcess ph

data Phase = Start | Stop deriving (Show)

phase :: Phase -> String -> IO ()
phase p msg = putStrLn $ printf "**** %s : %s **************************************" (show p) msg

writeLoud :: String -> IO ()
writeLoud s = whenLoud $ putStrLn s >> hFlush stdout

ensurePath :: FilePath -> IO ()
ensurePath = createDirectoryIfMissing True . takeDirectory

safeReadFile :: FilePath -> IO (Either String String)
safeReadFile f = (Right <$> readFile f) `catch` handleIO f

handleIO :: FilePath -> IOException -> IO (Either String a)
handleIO f e = return . Left $ "Warning: Couldn't open " <> f <> ": " <> show e

traceShow :: (Show a) => String -> a -> a
traceShow msg x = {- trace (printf "TRACE: %s = %s" msg (show x)) -} x

safeHead :: a -> [a] -> a
safeHead def []    = def
safeHead _   (x:_) = x

getRange :: Int -> Int -> [a] -> [a]
getRange i1 i2
  = take (i2 - i1 + 1)
  . drop (i1 - 1)
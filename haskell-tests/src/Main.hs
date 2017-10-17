 
module Main ( main ) where

import Data.List ( foldl1 )
import Data.Proxy ( Proxy(..) )
import Control.Monad ( void, forM )
import Text.Read ( readMaybe )
import System.Environment ( getArgs )
import Test.QuickCheck ( Result )

import Test.Utilities ( (&&&&) )
import Test.Types ( IntMod2 , IntMod3, NonCongruentIntMod2 )

import Test.Laws.Eq ( checkEq )
import Test.Laws.Ord ( checkOrd )
import Test.Laws.Set.Functor ( checkSetFunctor )
import Test.Laws.Set.Applicative ( checkSetApplicative )
import Test.Laws.Endo.Functor ( checkEndoFunctor )
import Test.Laws.Endo.Applicative ( checkFailEndoApplicative )
import Test.Laws.ListSet ( checkAllListSet )


options :: [(String, Int -> IO Result)]
options = 
  [ ("functor.set"      , \n -> checkSetFunctor n (Proxy :: Proxy (Int, Bool, String))
                           &&&& checkSetFunctor n (Proxy :: Proxy (Int, IntMod2, IntMod3))
                           )
  , ("functor.endo"     , \n -> checkEndoFunctor n (Proxy :: Proxy Int) 
                           &&&& checkEndoFunctor n (Proxy :: Proxy IntMod2) 
                           &&&& checkEndoFunctor n (Proxy :: Proxy NonCongruentIntMod2)
                           )
  , ("applicative.set"  , \n -> checkSetApplicative n (Proxy :: Proxy (Int, Bool, String, IntMod2))
                           &&&& checkSetApplicative n (Proxy :: Proxy (Int, IntMod3, Bool, IntMod2))
                           )
  , ("applicative.endo" , \n -> checkFailEndoApplicative n (Proxy :: Proxy Int) 
                           &&&& checkFailEndoApplicative n (Proxy :: Proxy IntMod2) 
                           &&&& checkFailEndoApplicative n (Proxy :: Proxy NonCongruentIntMod2)
                           )
  , ("eq" , \n -> checkEq n (Proxy :: Proxy IntMod2) 
             &&&& checkEq n (Proxy :: Proxy IntMod3)
             )
  , ("ord", \n -> checkOrd n (Proxy :: Proxy IntMod2) 
             &&&& checkOrd n (Proxy :: Proxy IntMod3)
             )
  , ("listset", \n -> checkAllListSet n (Proxy :: Proxy (Int,String))
             )
  ]

printHelp :: IO ()
printHelp = do
  putStrLn "test-laws [test] [amount]"
  putStrLn "  [test] - Set of laws to execute."
  putStrLn "  [number] - Number of test to execute for each law."
  putStrLn "Available sets of laws:"
  putStrLn "  all"
  void $ forM options $ \(set, _) -> putStrLn ("  " ++ set)

runAllTests :: Int -> IO ()
runAllTests n = void $ foldl1 (&&&&) $ fmap (($ n) . snd) options

defaultNumberOfTests :: Int
defaultNumberOfTests = 100

run :: String -> Int -> IO ()
run set n = case set of
  "all" -> runAllTests (abs n)
  _ -> case lookup set options of
    Just laws -> void $ laws (abs n)
    Nothing -> printHelp

main :: IO ()
main = do
  args <- getArgs
  case args of
    [set] -> run set defaultNumberOfTests
    (set : nStr : _) -> case readMaybe nStr of
      Just n -> run set n
      Nothing -> run set defaultNumberOfTests
    _ -> printHelp
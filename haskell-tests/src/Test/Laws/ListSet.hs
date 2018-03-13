
{-# LANGUAGE ScopedTypeVariables #-}

module Test.Laws.ListSet where

import Prelude 
  ( Ord(..), Eq(..), Show
  , Bool(..), Int, IO
  , ($), otherwise
  )

import Data.Typeable
import Data.Proxy
import Data.Set ( Set )
import qualified Data.Set as S

import Control.Arrow ( (***) )

import Test.QuickCheck
import Test.QuickCheck.Function

import Test.Utilities

checkAllListSet :: forall a b c d.
                 ( Function a, CoArbitrary a, Arbitrary a, Typeable a, Show a, Ord a
                 , Function b, CoArbitrary b, Arbitrary b, Typeable b, Show b, Ord b
                 ) => Int -> Proxy (a,b) -> IO Result
checkAllListSet n p = check n (Proxy :: Proxy (a , b)) "nub.map.nub == nub.map" lawNubMapNub
                 &&&& check n (Proxy :: Proxy (a , b)) "remove.nub.map.remove == remove.nub.map" lawRemoveMapNub
                 &&&& check n (Proxy :: Proxy (a , b)) "remove.map.remove == remove.map" lawRemoveMapRemove
                 &&&& check n (Proxy :: Proxy (a , b)) "insert.map == map.insert" lawInsertMap
                 &&&& check n (Proxy :: Proxy (a , b)) "sort.map.sort == sort.map" lawSortMapSort
                 &&&& check n (Proxy :: Proxy (a , b)) "sort.insert.map = sort.map.insert" lawSortInsertMap

remove :: (Eq a) => a -> [a] -> [a]
remove y [] = []
remove y (x : xs) | y == x = remove y xs
remove y (x : xs) | otherwise = x : remove y xs

nub :: (Eq a) => [a] -> [a]
nub [] = []
nub (x : xs) = x : remove x (nub xs)

insert :: (Ord a) => a -> [a] -> [a]
insert x [] = x : []
insert x (y : ys) | x <= y = x : y : ys
insert x (y : ys) | otherwise = y : insert x ys

map :: (Ord a, Ord b) => (a -> b) -> [a] -> [b]
map f [] = []
map f (x : xs) = insert (f x) (map f xs)

sort :: (Ord a) => [a] -> [a] 
sort  [] = []
sort  (x : xs) = insert x (sort  xs)

union :: (Ord a) => [a] -> [a] -> [a]
union [] ys = ys
union (x : xs) ys = insert x (union xs ys)

unions :: (Ord a) => [[a]] -> [a]
unions [] = []
unions (xs : xss) = union xs (unions xss)

ap :: (Ord a, Ord b) => ([a] , [b]) -> [(a , b)]
ap ([] , ys) = []
ap (x : xs , ys) = union (map (\y -> (x , y)) ys) (ap (xs , ys))

pure :: (Ord a) => a -> [a]
pure a = [a]

lawNubMapNub :: forall a b. (Ord a, Ord b) => Proxy (a,b) -> Fun a b -> [a] -> Bool
lawNubMapNub _ f' as = nub (map f (nub as)) == nub (map f as)
  where f = apply f'

lawRemoveMapNub :: forall a b. (Ord a, Ord b) => Proxy (a,b) -> Fun a b -> a -> [a] -> Bool
lawRemoveMapNub _ f' a as = remove (f a) (nub (map f (remove a as))) == remove (f a) (nub (map f as))
  where f = apply f'

lawRemoveMapRemove :: forall a b. (Ord a, Ord b) => Proxy (a,b) -> Fun a b -> a -> [a] -> Bool
lawRemoveMapRemove _ f' a as = remove (f a) (map f (remove a as)) == remove (f a) (map f as)
  where f = apply f'

lawInsertMap :: forall a b. (Ord a, Ord b) => Proxy (a,b) -> Fun a b -> a -> [a] -> Bool
lawInsertMap _ f' a as = insert (f a) (map f as) == map f (insert a as)
  where f = apply f'

lawSortMapSort :: forall a b. (Ord a, Ord b) => Proxy (a,b) -> Fun a b -> [a] -> Bool
lawSortMapSort _ f' as = sort (map f (sort as)) == sort (map f as)
  where f = apply f'

lawSortInsertMap :: forall a b. (Ord a, Ord b) => Proxy (a,b) -> Fun a b -> a -> [a] -> Bool
lawSortInsertMap _ f' a as = sort (insert (f a) (map f as)) == sort ((map f (insert a as)))
  where f = apply f'

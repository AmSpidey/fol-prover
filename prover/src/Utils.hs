{-# LANGUAGE ParallelListComp #-}

module Utils where

import Data.List hiding (tails)
import Test.QuickCheck
import System.IO.Unsafe

-- useful for debugging
debug :: Show a => String -> a -> a
debug str x = seq (unsafePerformIO $ do putStr "<"; putStr str; putStr ": "; print x; putStr ">") x

update :: Eq a => (a -> b) -> a -> b -> a -> b
update f a b = \x -> if x == a then b else f x

partitions :: [a] -> [[[a]]]
partitions [] = [[]]
partitions (x:xs) = [[x]:yss | yss <- partitions xs] ++ [(x:ys):yss | (ys:yss) <- partitions xs]

-- all possible ways to split n into the sum of stricly positive integers
catalan :: Int -> [[Int]]
catalan n = map (map length) $ partitions [1..n]

-- alternating merge of two (potentially infinite) lists
merge :: [a] -> [a] -> [a]
merge [] bs = bs
merge (a : as) bs = a : merge bs as

-- alternating merge of a (potentially infinite) list of (potentially infinite) lists
merges :: [[a]] -> [a]
merges [] = []
merges (as:ass) = merge as (merges ass)

-- collect all functions from a finite list to a (potentially infinite) list
functions :: Eq a => [a] -> [b] -> [a -> b]
functions [] _ = [undefined]
functions (a:as) bs = merges [[update f a b | f <- functions as bs] | b <- bs]

-- find all ways of joining the lists
distribute :: [[a]] -> [[a]] -> [[a]]
distribute xss yss = go xss yss yss where
  go [] _ _ = []
  go (_:xss) yss [] = go xss yss yss
  go (xs:xss) yss (ys:yss') = (xs ++ ys) : go (xs:xss) yss yss'

combWithRep :: Int -> [a] -> [[a]]
combWithRep 0 l = []
combWithRep 1 l = [[x] | x <- l]
combWithRep k l = distribute (combWithRep (k - 1) l) [[x] | x <- l]

replaceComb :: [a] -> [b] -> [[(a, b)]]
replaceComb vars ts = [zip vars z | z <- combWithRep (length vars) ts]

splitEvery :: Int -> [a] -> [[a]]
splitEvery _ [] = []
splitEvery n list = first : splitEvery n rest
  where
    (first,rest) = splitAt n list

allSuffixes :: Int -> [a] -> [[a]]
allSuffixes n x = [concat $ take k (splitEvery n x) | k <- [1..length $ splitEvery n x]]

remSuperList :: Eq a => [[a]] -> [[a]]
remSuperList l = go l l where
    go :: Eq a => [[a]] -> [[a]] -> [[a]]
    go [] _ = []
    go (l:lt) f = if isSuperList l f then go lt f else l : go lt f

    isSuperList :: Eq a => [a] -> [[a]] -> Bool
    isSuperList l f = or [intersect l ls == ls && length l > length ls | ls <- f]

lsort :: [[a]] -> [[a]]
lsort = sortOn length
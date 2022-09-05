module AuxiliaryFunctions where

import Data.List

rmdups :: Eq a => [a] -> [a]
rmdups [] = []
rmdups (x:xs) | x `elem` xs   = rmdups xs
              | otherwise     = x : rmdups xs

subsets :: Eq a => [a] -> [[a]]
subsets [] = [[]]
subsets (x:xs) = yss ++ map (x:) yss
    where yss = subsets xs

seplegal :: Ord a => [a] -> [a] -> Bool
seplegal xs ys = sort xs == sort ys

contextsep :: Ord a => [a] -> [([a],[a])]
contextsep xs = rmdups [(f,s) | f <- subsets xs, s <- subsets xs, seplegal (f ++ s) xs]

pick3 :: Eq a => [a] -> [[a]]
pick3 xs = [s | s <- subsets xs, length s == 3]

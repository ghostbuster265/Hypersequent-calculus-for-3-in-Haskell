module AuxiliaryFunctions where

-----------

subsets :: Eq a => [a] -> [[a]]
subsets [] = [[]]
subsets (x:xs) = yss ++ map (x:) yss
    where yss = subsets xs

seplegal :: Eq a => [a] -> [a] -> Bool
seplegal [] _ = True
seplegal _ [] = True
seplegal xs ys = not (elem xs (subsets ys)) && not (elem ys (subsets xs))

contextsep :: Eq a => [a] -> [([a],[a])]
contextsep xs = [(f,s) | f <- subsets xs, s <- subsets xs, length f + length s == length xs, seplegal f s]

pick3 :: Eq a => [a] -> [[a]]
pick3 xs = [s | s <- subsets xs, length s == 3]
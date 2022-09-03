module AuxiliaryFormulas where

import Language
import Data.List

checkform :: [For] -> [For] -> Bool
checkform [] ys = False
checkform (x:xs) ys = case x of
	N z -> z `elem` ys || checkform xs ys
	z -> (N z) `elem` ys || checkform xs ys

var :: For -> Bool
var x = case x of
    V _ -> True
    N (V _) -> True
    _ -> False

------------------------------------------------------

nonbranchingL :: For -> Bool
nonbranchingL x = case x of
    A _ _ -> True
    N _ -> True
    _     -> False

branchingL :: For -> Bool
branchingL x = case x of
    D _ _ -> True
    _     -> False

nonbranchingR :: For -> Bool
nonbranchingR x = case x of
    D _ _ -> True
    I3 _ _ -> True
    N _ -> True
    _     -> False

branchingR :: For -> Bool
branchingR x = case x of
    A _ _ -> True
    _     -> False

contextImp :: For -> Bool
contextImp x = case x of
    I3 _ _ -> True
    _ -> False
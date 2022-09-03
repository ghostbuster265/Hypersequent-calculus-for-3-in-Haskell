module L3 where

import Language
--import LanguageMbC
import Data.Tree
import Data.List
import AuxiliaryFunctions
import AuxiliaryFormulas

l3_orderseq :: L3Seq -> L3Seq
l3_orderseq (L3S (L3 (xs, ys, zs, is), (L3 (xs', ys', zs', is')))) = L3S (l3_insertcontextL (xs ++ ys ++ zs ++ is) (L3 ([],[],[],[])), l3_insertcontextR (xs' ++ ys' ++ zs' ++ is') (L3 ([],[],[],[])))

-- | Insert a singular formula in a proper list in a sequent, depending on its form seperately for the right and left side of a sequent (functions l3_insertL and l3_insertR)
l3_insertL :: For -> L3SeqSide -> L3SeqSide
l3_insertL f (L3 (xs, ys, zs, is))
	| var f            = L3 (f:xs, ys, zs, is)
	| nonbranchingL f  = L3 (xs, f:ys, zs, is)
	| branchingL f     = L3 (xs, ys, f:zs, is)
	| contextImp f     = L3 (xs, ys, zs, f:is)

l3_insertR :: For -> L3SeqSide -> L3SeqSide
l3_insertR f (L3 (xs, ys, zs, is))
	| var f            = L3 (f:xs, ys, zs, is)
	| nonbranchingR f  = L3 (xs, f:ys, zs, is)
	| branchingR f     = L3 (xs, ys, f:zs, is)

l3_insertcontextL :: [For] -> L3SeqSide -> L3SeqSide
l3_insertcontextL [] s = s
l3_insertcontextL (f:fs) s = l3_insertcontextL fs (l3_insertL f s)

l3_insertcontextR :: [For] -> L3SeqSide -> L3SeqSide
l3_insertcontextR [] s = s
l3_insertcontextR (f:fs) s = l3_insertcontextR fs (l3_insertR f s)

-- | Generating all the possible separation of  
l3_sepcontexts :: [L3Seq] -> [L3Seq] -> [(([L3Seq],[L3Seq]),([For],[For]),([For],[For]))]
l3_sepcontexts (x:xs) g
	| l3_atomicseq x = l3_sepcontexts xs g
	| otherwise = case x of
		L3S (L3 (xs',ys,zs, I3 m n:is), L3 (xs'',ys',zs',_)) -> [(h,l,r) | h <- contextsep (delete x g), l <- contextsep (xs' ++ ys ++ zs ++ is), r <- contextsep (xs'' ++ ys' ++ zs')]
l3_sepcontexts [] _ = []

l3_mixingruleHypL :: [L3Seq] -> [For] -> [For] -> [L3Seq] -> [L3Seq]
l3_mixingruleHypL (x:xs) ls rs (m1:m2:m3:[]) = [L3S (l3_insertcontextL ls (L3 ([],[],[],[])), l3_insertcontextR rs (L3 ([],[],[],[])))] ++ (delete m3 (delete m2 (delete m1 xs)))

l3_mixingruleHypR :: [L3Seq] -> [For] -> [For] -> [L3Seq] -> [L3Seq]
l3_mixingruleHypR (x:xs) ls rs (m1:m2:m3:[]) = [L3S (l3_insertcontextL ls (L3 ([],[],[],[])), l3_insertcontextR rs (L3 ([],[],[],[])))] ++ (delete m3 (delete m2 (delete m1 xs)))

l3_contextruleHypR :: [L3Seq] -> [L3Seq] -> [For] -> [For] -> [L3Seq]
l3_contextruleHypR (x:xs) hs ls rs
	| l3_atomicseq x = (l3_contextruleHypR xs hs ls rs)
	| otherwise = case x of
		L3S (L3 (_,_,_, I3 _ n:is), r) -> [L3S (l3_insertL n (l3_insertcontextL ls (L3 ([],[],[],[]))), l3_insertcontextR rs (L3 ([],[],[],[])))] ++ hs
l3_contextruleHypR [] _ _ _ = []

l3_contextruleHypL :: [L3Seq] -> [L3Seq] -> [For] -> [For] -> [L3Seq]
l3_contextruleHypL (x:xs) hs ls rs
	| l3_atomicseq x = (l3_contextruleHypL xs hs ls rs)
	| otherwise = case x of
		L3S (L3 (_,_,_, I3 m _:is), r) -> [L3S (l3_insertcontextL ls (L3 ([],[],[],[])), l3_insertR m (l3_insertcontextR rs (L3 ([],[],[],[]))))] ++ hs
l3_contextruleHypL [] _ _ _ = []

l3_branchingruleHypR :: [L3Seq] -> [L3Seq]
l3_branchingruleHypR (x:xs)
	| l3_atomicseq x || l3_contextseq x = (x:l3_branchingruleHypR xs)
	| otherwise = case x of
		L3S (L3 (xs',ys, D _ n:zs,is), r) -> [L3S (l3_insertL n (L3 (xs',ys,zs,is)), r)] ++ xs
		L3S (l, L3 (xs',ys, A _ n:zs,is)) -> [L3S (l, l3_insertR n (L3 (xs',ys,zs,is)))] ++ xs
l3_branchingruleHypR [] = []

l3_branchingruleHypL :: [L3Seq] -> [L3Seq]
l3_branchingruleHypL (x:xs)
	| l3_atomicseq x || l3_contextseq x = (x:l3_branchingruleHypL xs)
	| otherwise = case x of
		L3S (L3 (xs',ys, D m _ :zs,is), r) -> [L3S (l3_insertL m (L3 (xs',ys,zs,is)), r)] ++ xs
		L3S (l, L3 (xs',ys, A m _ :zs,is)) -> [L3S (l, l3_insertR m (L3 (xs',ys,zs,is)))] ++ xs
l3_branchingruleHypL [] = []

-- | Applying function l3_nonbranchingruleSeq on a given hypersequent.*
l3_nonbranchingruleHyp :: [L3Seq] -> [L3Seq]
l3_nonbranchingruleHyp (x:xs) 
	| l3_branchingseq x || l3_atomicseq x || l3_contextseq x = (x:l3_nonbranchingruleHyp xs)
	| otherwise = case x of
		L3S (L3 (xs', N f:ys,zs,is), r) -> [L3S (L3 (xs',ys,zs,is), l3_insertR f r)] ++ xs
		L3S (L3 (xs', A m n:ys,zs,is), r) -> [L3S (l3_insertL m (L3 (xs',ys,zs,is)), r), L3S (l3_insertL n (L3 (xs',ys,zs,is)), r)] ++ xs
		L3S (l, L3 (xs', N f:ys,zs,is)) -> [L3S (l3_insertL f l, L3 (xs',ys,zs,is))] ++ xs
		L3S (l, L3 (xs', D m n:ys,zs,is)) -> [L3S (l, l3_insertR m (L3 (xs',ys,zs,is))), L3S (l, l3_insertR n (L3 (xs',ys,zs,is)))] ++ xs
		L3S (l, L3 (xs', I3 m n:ys,zs,is)) -> [L3S (l3_insertL m l, l3_insertR n (L3 (xs',ys,zs,is)))] ++ xs
l3_nonbranchingruleHyp [] = []

l3_triplebranchingR :: [L3Seq] -> [L3Seq]
l3_triplebranchingR (x:xs) = case x of
	L3S (L3 (x,y,z, I3 _ n:is), r) -> [L3S (l3_insertL n (L3 (x,y,z,is)), r)]
	_ -> l3_triplebranchingR (xs)
l3_triplebranchingR [] = []

l3_triplebranchingM :: ([L3Seq],[L3Seq]) -> [L3Seq]
l3_triplebranchingM ((x:xs),(l':m':r':[])) = case x of
	L3S (L3 (x,y,z, I3 m n:is), r) -> [L3S (l3_insertL n (L3 ([],[],[],[])), L3 ([],[],[],[])),m',L3S (L3 ([],[],[],[]), l3_insertR m (L3 ([],[],[],[])))] ++ (delete r' (delete m' (delete r' xs)))
	_ -> l3_triplebranchingM (xs,(l':m':r':[]))
l3_triplebranchingM ([],_) = []

l3_triplebranchingL :: [L3Seq] -> [L3Seq]
l3_triplebranchingL (x:xs) = case x of
	L3S (L3 (x,y,z, I3 m _:is), r) -> [L3S (L3 (x,y,z,is), l3_insertR m r)]
	_ -> l3_triplebranchingL (xs)
l3_triplebranchingL [] = []
----------------------------------------------------------------------------------------------------------------------------------------
	
-- | Checks if a given sequent is an atomic one, that is, there are only variables left and nothing left to resolve.
l3_contextseq :: L3Seq -> Bool
l3_contextseq (L3S (L3 (x, y, z, i),L3 (x', y', z', _))) = if null (y ++ z ++ y' ++ z') && not (null i) then True else False

-- | Checks if a given sequent is an atomic one, that is, there are only variables left and nothing left to resolve.
l3_atomicseq :: L3Seq -> Bool
l3_atomicseq (L3S (L3 (_, y, z, i),L3 (_, y', z', _))) = if null (y ++ z ++ i ++ y' ++ z') then True else False

-- | Checks if there are no non-branching formulas in a sequent
l3_branchingseq :: L3Seq -> Bool
l3_branchingseq (L3S (L3 (_, ys, _, _),L3 (_, ys', _, _))) = if null (ys ++ ys') then True else False

l3_branching :: [L3Seq] -> Bool
l3_branching xs = all l3_branchingseq xs

-- | Builds a tree for an argument of a tree type.
l3_buildcontextTree :: LT -> LT
l3_buildcontextTree (Leaf3 x)
    	| and (map (\s -> l3_atomicseq s || l3_contextseq s) x) = (Leaf3 x)
        | not (l3_branching x) = (Node3 x (Leaf3 (l3_nonbranchingruleHyp x)))
		| otherwise = (BranchingNode3 x (Leaf3 (l3_branchingruleHypL x)) (Leaf3 (l3_branchingruleHypR x)))
l3_buildcontextTree (Node3 x ch) = Node3 x (l3_buildcontextTree ch)
l3_buildcontextTree (BranchingNode3 x l r) = BranchingNode3 x (l3_buildcontextTree l) (l3_buildcontextTree r)
l3_buildcontextTree (TrippleNode3 x l m r) = TrippleNode3 x (l3_buildcontextTree l) (l3_buildcontextTree m) (l3_buildcontextTree r)

l3_insertContext :: LT -> (([L3Seq],[L3Seq]),([For],[For]),([For],[For])) -> LT
l3_insertContext (Leaf3 x) (h,l,r)
    	| all l3_atomicseq x = (Leaf3 x)
		| otherwise = (BranchingNode3 x (Leaf3 (l3_contextruleHypL x (fst h) (fst l) (fst r))) (Leaf3 (l3_contextruleHypR x (snd h) (snd l) (snd r))))
l3_insertContext (Node3 x ch) c = Node3 x (l3_insertContext ch c)
l3_insertContext (BranchingNode3 x l r) c
	| not (l3_atomTree l) = BranchingNode3 x (l3_insertContext l c) r
	| otherwise = BranchingNode3 x l (l3_insertContext r c)
l3_insertContext (TrippleNode3 x l m r) c
	| not (l3_atomTree l) = TrippleNode3 x (l3_insertContext l c) m r
	| not (l3_atomTree m) = TrippleNode3 x l (l3_insertContext m c) r
	| otherwise = TrippleNode3 x l m (l3_insertContext r c)

l3_posscontexts :: LT -> [(([L3Seq],[L3Seq]),([For],[For]),([For],[For]))]
l3_posscontexts (Leaf3 x) = l3_sepcontexts x x
l3_posscontexts (Node3 x ch) = l3_posscontexts ch
l3_posscontexts (BranchingNode3 x l r)
	| not (l3_atomTree l) = l3_posscontexts l
	| otherwise = l3_posscontexts r
l3_posscontexts (TrippleNode3 x l m r)
	| not (l3_atomTree l) = l3_posscontexts l
	| not (l3_atomTree m) = l3_posscontexts m
	| otherwise = l3_posscontexts r

l3_altTrees :: LT -> [LT]
l3_altTrees t = [l3_insertContext t c | c <- l3_posscontexts t]

l3_insertMixed :: LT -> (([For],[For]),([For],[For])) -> [L3Seq] -> LT
l3_insertMixed (Leaf3 x) (l,r) mixed = (BranchingNode3 x (Leaf3 (l3_mixingruleHypL x (fst l) (fst r) mixed)) (Leaf3 (l3_mixingruleHypR x (snd l) (snd r) mixed)))
l3_insertMixed (Node3 x ch) c mixed = Node3 x (l3_insertMixed ch c mixed)
l3_insertMixed (BranchingNode3 x l r) c mixed
	| l3_mixTree l = BranchingNode3 x (l3_insertMixed l c mixed) r
	| otherwise = BranchingNode3 x l (l3_insertMixed r c mixed)
l3_insertMixed (TrippleNode3 x l m r) c mixed
	| l3_mixTree l = TrippleNode3 x (l3_insertMixed l c mixed) m r
	| l3_mixTree m = TrippleNode3 x l (l3_insertMixed m c mixed) r
	| otherwise = TrippleNode3 x l m (l3_insertMixed r c mixed)

l3_tripleTree :: LT -> LT
l3_tripleTree (Leaf3 x) = TrippleNode3 x (Leaf3 (l3_triplebranchingL (fst trippled))) (Leaf3 (l3_triplebranchingM trippled)) (Leaf3 (l3_triplebranchingR (fst trippled)))
	where trippled = l3_tripleseq x x
l3_tripleTree (Node3 x ch) = Node3 x (l3_tripleTree ch)
l3_tripleTree (BranchingNode3 x l r)
	| l3_contextTree l = BranchingNode3 x (l3_tripleTree l) r
	| otherwise = BranchingNode3 x l (l3_tripleTree r)
l3_tripleTree (TrippleNode3 x l m r)
	| l3_contextTree l = TrippleNode3 x (l3_tripleTree l) m r
	| l3_contextTree m = TrippleNode3 x l (l3_tripleTree m) r
	| otherwise = TrippleNode3 x l m (l3_tripleTree r)

l3_tripleseq :: [L3Seq] -> [L3Seq] -> ([L3Seq],[L3Seq])
l3_tripleseq (x:xs) h = case x of
	L3S (L3 (x',y,z, I3 m n:is), r) -> ([L3S (L3 (x',y,z, I3 m n:is), r),L3S (L3 (x',y,z,is), r),L3S (L3 (x',y,z, I3 m n:is), r)] ++ (delete (L3S (L3 (x',y,z, I3 m n:is), r)) h),[L3S (L3 (x',y,z, I3 m n:is), r),L3S (L3 (x',y,z,is), r),L3S (L3 (x',y,z, I3 m n:is), r)])
	_ -> l3_tripleseq xs h

l3_mixcontexts :: [L3Seq] -> [(([For],[For]),([For],[For]))]
l3_mixcontexts [L3S (L3 (xs1,ys1,zs1,is1), L3 (xs1',ys1',zs1',is1')),L3S (L3 (xs2,ys2,zs2,is2), L3 (xs2',ys2',zs2',is2')),L3S (L3 (xs3,ys3,zs3,is3), L3 (xs3',ys3',zs3',is3'))] =
	[((ll1 ++ ll2 ++ ll3, lr1 ++ lr2 ++ lr3), (rl1 ++ rl2 ++ rl3, rr1 ++ rr2 ++ rr3)) |
		ll1 <- map (fst) s1, ll2 <- map (fst) s2, ll3 <- map (fst) s3,
		lr1 <- map (snd) s1, lr2 <- map (snd) s2, lr3 <- map (snd) s3,
		rl1 <- map (fst) s1', rl2 <- map (fst) s2', rl3 <- map (fst) s3',
		rr1 <- map (snd) s1', rr2 <- map (snd) s2', rr3 <- map (snd) s3',
		seplegal (ll1 ++ ll2 ++ ll3)  (lr1 ++ lr2 ++ lr3), seplegal (rl1 ++ rl2 ++ rl3) (rr1 ++ rr2 ++ rr3)]
		where (s1,s2,s3,s1',s2',s3') = ((contextsep (xs1 ++ ys1 ++ zs1 ++ is1)), (contextsep (xs2 ++ ys2 ++ zs2 ++ is2)), (contextsep (xs3 ++ ys3 ++ zs3 ++ is3)),
			  (contextsep (xs1' ++ ys1' ++ zs1' ++ is1')), (contextsep (xs2' ++ ys2' ++ zs2' ++ is2')), (contextsep (xs3'++ ys3' ++ zs3' ++ is3')))

l3_pick3 :: LT -> [[L3Seq]]
l3_pick3 (Leaf3 x) = pick3 x
l3_pick3 (Node3 _ ch) = l3_pick3 ch
l3_pick3 (BranchingNode3 _ l r)
	| l3_mixTree l = l3_pick3 l
	| otherwise = l3_pick3 r
l3_pick3 (TrippleNode3 _ l m r)
	| l3_mixTree l = l3_pick3 l
	| l3_mixTree m = l3_pick3 m
	| otherwise = l3_pick3 r 

l3_mixedTrees :: LT -> [[L3Seq]] -> [LT]
l3_mixedTrees t (x:xs) = [l3_insertMixed t c x | c <- l3_mixcontexts x] ++ (l3_mixedTrees t xs)
l3_mixedTrees t [] = []

l3_mixTree :: LT -> Bool
l3_mixTree (Leaf3 x) = length x > 2
l3_mixTree (Node3 _ ch) = l3_mixTree ch
l3_mixTree (BranchingNode3 _ l r) = (l3_mixTree l) || (l3_mixTree r)
l3_mixTree (TrippleNode3 _ l m r) = (l3_mixTree l) || (l3_mixTree m) || (l3_mixTree r)

-- | Checks if all of the leaves in a tree are atomic, so there is nothing left to resolve.
l3_contextTree :: LT -> Bool
l3_contextTree (Leaf3 x) = if all l3_contextseq x then True else False
l3_contextTree (Node3 _ ch) = l3_contextTree ch
l3_contextTree (BranchingNode3 _ l r) = (l3_contextTree l) && (l3_contextTree r)
l3_contextTree (TrippleNode3 _ l m r) = (l3_contextTree l) && (l3_contextTree m) && (l3_contextTree r)

l3_atomTree :: LT -> Bool
l3_atomTree (Leaf3 x) = if all l3_atomicseq x then True else False
l3_atomTree (Node3 _ ch) = l3_atomTree ch
l3_atomTree (BranchingNode3 _ l r) = (l3_atomTree l) && (l3_atomTree r)
l3_atomTree (TrippleNode3 _ l m r) = (l3_atomTree l) && (l3_atomTree m) && (l3_atomTree r)

l3_buildTrees :: [LT] -> [LT]
l3_buildTrees [] = []
l3_buildTrees (t:ts)
	| l3_isProof t = t : (l3_buildTrees ts)
	| not (l3_atomTree t) && not (l3_contextTree t) = (l3_buildcontextTree t) : ts
	| l3_mixTree t = case () of
		() | any l3_isProof (l3_derHyp (l3_mixedTrees t (l3_pick3 t))) -> (l3_mixedTrees t (l3_pick3 t)) ++ ts
		   | l3_contextTree t -> if any l3_isProof (l3_derHyp (l3_altTrees t)) then (l3_altTrees t) ++ ts else [l3_tripleTree t] ++ ts
		   | otherwise -> l3_buildTrees ts
	| l3_contextTree t = if any l3_isProof (l3_derHyp (l3_altTrees t)) then (l3_altTrees t) ++ ts else [l3_tripleTree t] ++ ts
	| otherwise = l3_buildTrees ts
	
l3_resolved :: [LT] -> Bool
l3_resolved ts = all l3_isProof ts

-- | Builds all derivation for a hypersequent until there are only atoms left starting with an initial leaf that contains the given hypersequent.
l3_derHyp :: [LT] -> [LT]
l3_derHyp x = until (l3_resolved) l3_buildTrees x 

l3_resolveHyp :: [L3Seq] -> [LT]
l3_resolveHyp x = l3_derHyp ([Leaf3 (map (\s -> l3_orderseq s) x)]) 

------------------------------------------------------------------------------------------------

l3_countBranches :: LT -> Int
l3_countBranches (Leaf3 _) = 1
l3_countBranches (Node3 _ ch) = l3_countBranches ch
l3_countBranches (BranchingNode3 _ l r) = (l3_countBranches l) + (l3_countBranches r)
l3_countBranches (TrippleNode3 _ l m r) = (l3_countBranches l) + (l3_countBranches m) + (l3_countBranches r)

l3_levels :: LT -> Int
l3_levels (Leaf3 _) = 1
l3_levels (Node3 _ ch) = 1 + (l3_levels ch)
l3_levels (BranchingNode3 _ l r) = 1 + (l3_levels l) + (l3_levels r)
l3_levels (TrippleNode3 _ l m r) = 1 + (l3_levels l) + (l3_levels m) + (l3_levels r)

l3_matchingformulas :: [For] -> [For] -> Bool
l3_matchingformulas [] ys = False
l3_matchingformulas (x:xs) ys = if x `elem` ys then True else l3_matchingformulas xs ys

l3_isAxiom :: L3Seq -> Bool
l3_isAxiom (L3S (L3 (xs, ys, zs, is), L3 (xs', ys', zs', is'))) = l3_matchingformulas l r || checkform l l || checkform r r
	where (l,r) = ((xs ++ ys ++ zs ++ is),(xs' ++ ys' ++ zs' ++ is'))

l3_isProof :: LT -> Bool
l3_isProof (Leaf3 x) = any (l3_isAxiom) x
l3_isProof (Node3 _ ch) = l3_isProof ch
l3_isProof (BranchingNode3 _ l r) = (l3_isProof l) && (l3_isProof r)
l3_isProof (TrippleNode3 _ l m r) = (l3_isProof l) && (l3_isProof m) && (l3_isProof r)

-----------------------------------------------------------------------------------------------

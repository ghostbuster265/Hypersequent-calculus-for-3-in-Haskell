module Language where

-- | Inductive definition of Formula type
data For =   Verum
            | V Int
            | N For     
            | For `I` For
            | For `A` For
            | For `D` For
            | For `I3` For deriving(Eq,Read,Show,Ord) -- L3 implication

------------------------------------------------------------------------------

data LT = Leaf3 [L3Seq] | Node3 [L3Seq] (LT) | BranchingNode3 [L3Seq] (LT) (LT) | TrippleNode3 [L3Seq] (LT) (LT) (LT) deriving (Eq,Show,Read,Ord)

newtype L3SeqSide = L3 ([For], [For], [For], [For]) deriving(Eq,Read,Show,Ord)
-- literals, non-branching formulas, branching formulas, implications that seperate contexts (on the right side the last set is empty)

newtype L3Seq = L3S (L3SeqSide, L3SeqSide) deriving(Eq,Read,Show,Ord)
-- (left side of sequent, right side of sequent)

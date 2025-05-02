module Algebra

import Data.Vect

import Tensor
import Tree
import Data.Rig


||| Generalised sum operation
||| Categorically, an F-Algebra
public export
interface Algebra (f : Type -> Type) a where
  constructor MkAlgebra
  reduce : f a -> a

public export
Rig a => Algebra List a where
  reduce = foldr (~+~) zero

-- Does this work for any Applicative? I think not, because in trees we have to choose an order of summation. But that might not impact things?
public export
{n : Nat} -> Rig a => Algebra (Vect n) a where
  reduce = foldr (~+~) zero

public export
[appSum] {shape : Vect n Nat} -> 
Rig a => Applicative f =>
Algebra (Tensor shape) (f a) using applicativeRig where
  reduce (TZ val) = val
  reduce (TS xs) = reduce (reduce <$> xs)

aa : Algebra (Tensor [2]) (Tensor [3] a) => a
aa = ?aa_rhs

||| Just summing up elements of the tree given by the Rig a structure
public export
Rig a => Algebra BTreeLeaf a where
  reduce (Leaf leaf) = leaf
  reduce (Node _ leftTree rightTree)
    = (reduce {f=BTreeLeaf} leftTree) ~+~ 
      (reduce {f=BTreeLeaf} rightTree)

-- can be simplified by uncommenting the Rig (f a) instance in Rig.idr
public export
[usualSum'] Rig a => Applicative f => Algebra BTreeLeaf (f a) where
  reduce (Leaf leaf) = leaf
  reduce (Node node leftTree rightTree)
    = let lt = reduce {f=BTreeLeaf} leftTree 
          rt = reduce {f=BTreeLeaf} rightTree
      in (uncurry (~+~)) <$> (liftA2 lt rt) 

public export
Rig a => Algebra BTreeNode a where
  reduce (Leaf _) = zero
  reduce (Node node leftTree rightTree) = node ~+~ (reduce {f=BTreeNode} leftTree) ~+~ (reduce {f=BTreeNode} rightTree)

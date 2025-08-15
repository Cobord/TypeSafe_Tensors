module Data.Algebra

import Data.Vect

import Data.Tree
import Misc


||| Generalised sum operation
||| Categorically, an F-Algebra
public export
interface Algebra (f : Type -> Type) a where
  constructor MkAlgebra
  reduce : f a -> a

public export
Num a => Algebra List a where
  reduce = foldr (+) (fromInteger 0)

-- Does this work for any Applicative? I think not, because in trees we have to choose an order of summation. But that might not impact things?
public export
{n : Nat} -> Num a => Algebra (Vect n) a where
  reduce = foldr (+) (fromInteger 0)

-- public export
-- [appSum] {shape : Vect n Nat} -> 
-- Num a => Applicative f =>
-- Algebra (TensorA shape) (f a) using applicativeNum where
--   reduce (TZ val) = val
--   reduce (TS xs) = reduce (reduce <$> xs)
-- 
-- aa : Algebra (TensorA [2]) (TensorA [3] a) => a
-- aa = ?aa_rhs

||| Summing up elements of the tree given by the Num a structure
public export
Num a => Algebra BinTreeLeaf a where
  reduce (Leaf leaf) = leaf
  reduce (Node _ leftTree rightTree)
    = (reduce {f=BinTreeLeaf} leftTree) + 
      (reduce {f=BinTreeLeaf} rightTree)

-- can be simplified by uncommenting the Num (f a) instance in Num.idr
public export
[usualSum'] Num a => Applicative f => Algebra BinTreeLeaf (f a) where
  reduce (Leaf leaf) = leaf
  reduce (Node node leftTree rightTree)
    = let lt = reduce {f=BinTreeLeaf} leftTree 
          rt = reduce {f=BinTreeLeaf} rightTree
      in (uncurry (+)) <$> (liftA2 lt rt) 

public export
Num a => Algebra BinTreeNode a where
  reduce (Leaf _) = fromInteger 0
  reduce (Node node leftTree rightTree)
     = node + (reduce {f=BinTreeNode} leftTree)
            + (reduce {f=BinTreeNode} rightTree)

module Data.Container.InstanceInterfaces

import Data.Vect
import Decidable.Equality


import Data.Container.Object.Definition
import Data.Container.Object.Instances
import Data.Container.Concrete.Definition
import Data.Container.Concrete.Instances
import Data.Container.Extension.Definition
import Data.Container.Extension.Instances
import Data.Container.Applicative.Definition
import Data.Container.Applicative.Instances

import Data.Tree
import Data.Algebra
import Misc

%hide Prelude.toList

namespace VectInstances
  public export
  {n : Nat} -> Eq x => Eq (Vect' n x) where
    v == v' = (toVect v) == (toVect v')
 
  public export
  {n : Nat} -> Show x => Show (Vect' n x) where
    show v = show (toVect v)

  public export
  {n : Nat} -> Foldable (Vect' n) where
    foldr f z v = foldr f z (toVect v)
  
  public export
  {n : Nat} -> Num a => Algebra (Vect' n) a where
    reduce v = reduce (toVect v)

{---
Ideally, all instances would be defined in terms of ConcreteTypes,
but there are totality checking issues with types whose size isn't known
at compile time
---}
namespace ListInstances
  ||| Not partial but not sure how to convince Idris totality checker
  partial
  public export
  Eq a => Eq (List' a) where
    l == l' = (toList l) == (toList l')

  ||| Not partial but not sure how to convince Idris totality checker
  partial
  public export
  Show a => Show (List' a) where
    show x = show (toList x)

  public export
  Foldable List' where
    foldr f z v = foldr f z (toList v)

  public export
  Num a => Algebra List' a where
    reduce = reduce {f=List} . toList


  -- some attempts at fixing partiality below
  -- public export
  -- showListHelper : Show a => List' a -> String
  -- showListHelper (0 <| _) = ""
  -- showListHelper (1 <| index) = show $ index FZ
  -- showListHelper ((S k) <| index)
  --   = let (s, rest) = removeBeginning index
  --     in show s ++ ", " ++ showListHelper (k <| rest)

  -- public export
  -- showListHelper : Show a => List' a -> String
  -- showListHelper x = show (toList x)


namespace BinTreeInstances
  ||| Not partial but not sure how to convince Idris totality checker
  partial
  public export
  Eq a => Eq (BinTree' a) where
    t == t' = (toBinTreeSame t) == (toBinTreeSame t')

  ||| Not partial but not sure how to convince Idris totality checker
  partial
  public export
  Show a => Show (BinTree' a) where
    show = show . toBinTreeSame

  ||| Summing up nodes and leaves of the tree given by the Num a structure
  public export
  Num a => Algebra BinTree' a where
    reduce = reduce {f=BinTreeSame} . toBinTreeSame

  public export
  binTreePosInterface : InterfaceOnPositions BinTree DecEq
  binTreePosInterface = MkI


namespace BinTreeLeafInstances
  ||| Not partial but not sure how to convince Idris totality checker
  partial
  public export
  Eq a => Eq (BinTreeLeaf' a) where
    t == t' = (toBinTreeLeaf t) == (toBinTreeLeaf t')

  ||| Not partial but not sure how to convince Idris totality checker
  partial
  public export
  Show a => Show (BinTreeLeaf' a) where
    show = show . toBinTreeLeaf

  ||| Summing up leaves of the tree given by the Num a structure
  public export
  Num a => Algebra BinTreeLeaf' a where
    reduce = reduce {f=BinTreeLeaf} . toBinTreeLeaf


namespace BinTreeNodeInstances
  ||| Not partial but not sure how to convince Idris totality checker
  partial
  public export
  Eq a => Eq (BinTreeNode' a) where
    t == t' = (toBinTreeNode t) == (toBinTreeNode t')

  ||| Not partial but not sure how to convince Idris totality checker
  partial
  public export
  Show a => Show (BinTreeNode' a) where
    show = show . toBinTreeNode

  ||| Summing up nodes of the tree given by the Num a structure
  public export
  Num a => Algebra BinTreeNode' a where
    reduce = reduce {f=BinTreeNode} . toBinTreeNode


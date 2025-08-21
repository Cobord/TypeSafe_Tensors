module Data.Container.InstanceInterfaces

import Data.Vect


import Data.Container.Object.Definition
import Data.Container.Object.Instances
import Data.Container.Concrete.Definition
import Data.Container.Concrete.Instances
import Data.Container.Extension.Definition
import Data.Container.Extension.Instances

import Data.Algebra
import Misc

-- TODO should all of these instances be defined in terms of their concrete ones?
-- i.e. simply via translation functions to concreteTypes we defined above?
namespace VectInstances
  public export
  {n : Nat} -> Eq x => Eq (Ext (Vect n) x) where
    v == v' = (toVect v) == (toVect v')
 
  public export
  {n : Nat} -> Show x => Show (Ext (Vect n) x) where
    show v = show (toVect v)

  public export
  {n : Nat} -> Foldable (Ext (Vect n)) where
    foldr f z v = foldr f z (toVect v)
  
  public export
  {n : Nat} -> Num a => Algebra (Ext (Vect n)) a where
    reduce v = reduce (toVect v)


  %hint
  public export
  vectInterfacePos : {n : Nat} -> InterfaceOnPositions Eq (Vect n)
  vectInterfacePos = PosInterface 

namespace ListInstances
  public export
  showListHelper : Show a => List' a -> String
  showListHelper (0 <| _) = ""
  showListHelper (1 <| indexCont) = show $ indexCont FZ
  showListHelper ((S k) <| indexCont)
    = let (s, rest) = removeBeginning indexCont
      in show s ++ ", " ++ showListHelper (k <| rest)

  ||| Not partial but not sure how to convince Idris totality checker
  partial 
  public export
  Show a => Show (List' a) where
    show x = "[" ++ showListHelper x ++ "]"



namespace BinTreeLeafInstances
  public export
  showBinTreeLeaf' : Show a => BinTreeLeaf' a -> String
  showBinTreeLeaf' (LeafS <| content) = "Leaf (" ++ show (content Done) ++ ")"
  showBinTreeLeaf' ((NodeS l r) <| content) =
    let leftSubtree : BinTreeLeaf' a = (l <| \posL => content (GoLeft posL))
        rightSubtree : BinTreeLeaf' a = (r <| \posR => content (GoRight posR))
    in "Node (" ++ showBinTreeLeaf' leftSubtree ++ ") (" ++ showBinTreeLeaf' rightSubtree ++ ")"

  -- this causes a compilation hang when toBinTreeLeaf is in a different file?

  -- partial
  -- public export
  -- Show a => Show (BinTreeLeaf' a) where
  --   show t = show (toBinTreeLeaf t)

  public export
  Eq a => Eq (BinTreeLeaf' a) where
    (LeafS <| v) == (LeafS <| v') = v Done == v' Done
    (NodeS l r <| v) == (NodeS l' r' <| v') =
      (l == l') && (r == r') && ?vnm -- Assuming Eq BinTreeShape is defined elsewhere
    _ == _ = False

  ||| Just summing up elements of the tree given by the Num a structure
  public export
  Num a => Algebra BinTreeLeaf' a where
    reduce (LeafS <| v) = v Done
    reduce (NodeS l r <| v) =
      let leftSubtree = l <| v . GoLeft
          rightSubtree = r <| v . GoRight
      in reduce {f=BinTreeLeaf'} leftSubtree +
         reduce {f=BinTreeLeaf'} rightSubtree



namespace BinTreeNodeInstances
  public export
  Num a => Algebra BinTreeNode' a where
    reduce (LeafS <| v) = fromInteger 0
    reduce (NodeS l r <| v) = v Done +
      reduce {f=BinTreeNode'} (l <| v . GoLeft) +
      reduce {f=BinTreeNode'} (r <| v . GoRight)


{-
namespace TensorInstances
  public export
  tensorReplicate : {shape : List Cont} ->
    a -> Tensor' shape a
  -- tensorReplicate {shape = []} a = fromIdentity a
  -- tensorReplicate {shape = (c :: cs)} a = ?vniuuu

  public export
  liftA2Tensor : {shape : List Cont} ->
    Tensor' shape a -> Tensor' shape b -> Tensor' shape (a, b)

  public export
  Applicative (Tensor' shape) where
    pure = ?vimmm -- tensorReplicate
    fs <*> xs = ?qivnfi -- uncurry ($) <$> liftA2Tensor fs xs

  -- public export
  -- {shape : List Cont} -> Num a => Num (Tensor' shape a) where
  --   fromInteger i = pure (fromInteger i)
  --   xs + ys = (uncurry (+)) <$> liftA2 xs ys
  --   xs * ys = (uncurry (*)) <$> liftA2 xs ys



public export
data AllAlgebra : (shape : List Cont) -> (dtype : Type) -> Type where
  Nil : AllAlgebra [] a
  Cons : {c : Cont} -> {cs : List Cont} ->
    (alg : Algebra (Ext c) (Tensor' cs a)) =>
    (allAlg : AllAlgebra cs a) =>
    AllAlgebra (c :: cs) a


public export
reduceTensor : {shape : List Cont} ->
  (allAlgebra : AllAlgebra shape a) =>
  Tensor' shape a -> a
-- reduceTensor {shape = []} {allAlgebra = []} t = toIdentity t
-- reduceTensor {shape = (c :: cs)} {allAlgebra = Cons {alg} {allAlg}} t
--   = ((reduceTensor {allAlgebra=allAlg}) . (reduce @{alg}))
--       (toContainerComp <$> (fromContainerComp {shape=(c :: cs)} t))

public export
{shape : List Cont} ->
(allAlgebra : AllAlgebra shape a) =>
Algebra (Tensor' shape) a where
  reduce = reduceTensor


agtest0 : Algebra BinTreeNode Int
agtest0 = %search

attt : AllAlgebra [] Int
attt = %search

-- attt1 : Algebra (Ext BinTreeNode) (Tensor' [] Int)
-- attt1 = %search
-- 
-- agt0 : AllAlgebra [BinTreeNode] Int
-- agt0 = %search
-- 
-- agt : AllAlgebra [BinTreeNode, Vect 7] Int
-- agt = %search
-- 
-- agtest : Algebra (Tensor' [BinTreeNode, Vect 7]) Int
-- agtest = %search
-}

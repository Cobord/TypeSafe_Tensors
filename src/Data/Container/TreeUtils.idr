module Data.Container.TreeUtils

||| Shapes of binary trees
public export
data BTreeShape : Type where
  LeafS : BTreeShape
  NodeS : BTreeShape -> BTreeShape -> BTreeShape

%name BTreeShape b, b1, b2, b3

public export
numLeaves : BTreeShape -> Nat
numLeaves LeafS = 1
numLeaves (NodeS lt rt) = numLeaves lt + numLeaves rt

public export
numNodes : BTreeShape -> Nat
numNodes LeafS = 0
numNodes (NodeS lt rt) = numNodes lt + (1 + numNodes rt)

public export
Eq BTreeShape where
  LeafS == LeafS = True
  NodeS l r == NodeS l' r' = l == l' && r == r'
  _ == _ = False

namespace BTree
  ||| Positions corresponding to internal nodes within a BTree shape that contains both nodes and leaves
  public export
  data FinBTree : (b : BTreeShape) -> Type where
    DoneLeaf : FinBTree LeafS
    DoneNode : {l, r : BTreeShape} -> FinBTree (NodeS l r)
    GoLeft : {l, r : BTreeShape} -> FinBTree l -> FinBTree (NodeS l r)
    GoRight : {l, r : BTreeShape} -> FinBTree r -> FinBTree (NodeS l r)

namespace BTreeNode
  ||| Positions corresponding to internal nodes within a BTreeNode shape.
  public export
  data FinBTreeNode : (b : BTreeShape) -> Type where
    Done : {l, r : BTreeShape} -> FinBTreeNode (NodeS l r)
    GoLeft  : {l, r : BTreeShape} -> FinBTreeNode l -> FinBTreeNode (NodeS l r)
    GoRight  : {l, r : BTreeShape} -> FinBTreeNode r -> FinBTreeNode (NodeS l r)

namespace BTreeLeaf
  ||| Positions corresponding to leaves within a BTreeLeaf shape.
  public export
  data FinBTreeLeaf : (b : BTreeShape) -> Type where
    Done : FinBTreeLeaf LeafS
    GoLeft : {l, r : BTreeShape} -> FinBTreeLeaf l -> FinBTreeLeaf (NodeS l r)
    GoRight : {l, r : BTreeShape} -> FinBTreeLeaf r -> FinBTreeLeaf (NodeS l r)

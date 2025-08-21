module Data.Container.TreeUtils

import Language.Reflection
import Derive.Prelude

import Data.Container.SubTerm
import Data.Container.Object.Definition
import Data.Container.Applicative.Definition

%language ElabReflection

{-----------------------------------------------------------
{-----------------------------------------------------------
This file defines the types of shapes and positions 
for various tree types for usage in containers.
All of the trees here are *finite*.

It defines the type of shapes of 
* Binary trees, together with the type of positions for
  * Binary trees with data stored both at nodes and leaves
  * Binary trees with data stored at nodes only
  * Binary trees with data stored at leaves only
* Rose trees, together with the type of positions for
  * Rose trees with data stored both at nodes and leaves
  * Rose trees with data stored at nodes only
  * Rose trees with data stored at leaves only
-----------------------------------------------------------}
-----------------------------------------------------------}


namespace BinaryTrees
  ||| Shapes of binary trees
  public export
  data BinTreeShape : Type where
    LeafS : BinTreeShape
    NodeS : BinTreeShape -> BinTreeShape -> BinTreeShape

  %runElab derive "BinTreeShape" [Eq, Show]
  %name BinTreeShape b, b1, b2, b3, b4, b5

  public export
  numLeaves : BinTreeShape -> Nat
  numLeaves LeafS = 1
  numLeaves (NodeS lt rt) = numLeaves lt + numLeaves rt
  
  public export
  numNodes : BinTreeShape -> Nat
  numNodes LeafS = 0
  numNodes (NodeS lt rt) = numNodes lt + (1 + numNodes rt)
  
  namespace NodesAndLeaves
    ||| Positions corresponding to both nodes and leaves within a BinTreeShape
    public export
    data BinTreePos : (b : BinTreeShape) -> Type where
      DoneLeaf : BinTreePos LeafS
      DoneNode : {l, r : BinTreeShape} -> BinTreePos (NodeS l r)
      GoLeft : {l, r : BinTreeShape} -> BinTreePos l -> BinTreePos (NodeS l r)
      GoRight : {l, r : BinTreeShape} -> BinTreePos r -> BinTreePos (NodeS l r)

    %runElab deriveIndexed "BinTreePos" [Eq, Show]

  ||| Check if a term is a subterm of another term
  ||| t1 < t2 means that t2 > t1
  public export
  MOrd (BinTreePos b) where
    mcompare DoneLeaf DoneLeaf = Just EQ
    mcompare DoneNode DoneNode = Just EQ
    mcompare (GoLeft b1) (GoLeft b2) = mcompare b1 b2
    mcompare (GoRight b1) (GoRight b2) = mcompare b1 b2
    mcompare DoneNode (GoLeft _) = Just LT
    mcompare DoneNode (GoRight _) = Just LT
    mcompare (GoLeft _) DoneNode = Just GT
    mcompare (GoRight _) DoneNode = Just GT
    mcompare (GoLeft _) (GoRight _) = Nothing -- they diverge
    mcompare (GoRight _) (GoLeft _) = Nothing -- they diverge
    -- for quantitave version of MOrd the last two should map to BinTreePos b extende with a negative direction

  data Dir : (a : Type) -> Type where
    Pos : a -> Dir a
    Neg : a -> Dir a

  Tr : BinTreeShape
  Tr = NodeS (NodeS LeafS LeafS) LeafS
    
  Path1 : BinTreePos Tr
  Path1 = GoLeft DoneNode

  Path2 : BinTreePos Tr
  Path2 = GoLeft (GoLeft DoneLeaf)

  Path3 : BinTreePos Tr
  Path3 = GoRight DoneLeaf

  fh : (mcompare Path1 Path2) = Just LT
  fh = ?asdf
  
  namespace Nodes
    ||| Positions corresponding to nodes within a BinTreeNode shape.
    public export
    data BinTreePosNode : (b : BinTreeShape) -> Type where
      Done : {l, r : BinTreeShape} -> BinTreePosNode (NodeS l r)
      GoLeft  : {l, r : BinTreeShape} -> BinTreePosNode l -> BinTreePosNode (NodeS l r)
      GoRight  : {l, r : BinTreeShape} -> BinTreePosNode r -> BinTreePosNode (NodeS l r)

    %runElab deriveIndexed "BinTreePosNode" [Eq, Show]
  
  namespace Leaves
    ||| Positions corresponding to leaves within a BinTreeShape 
    public export
    data BinTreePosLeaf : (b : BinTreeShape) -> Type where
      Done : BinTreePosLeaf LeafS
      GoLeft : {l, r : BinTreeShape} -> BinTreePosLeaf l -> BinTreePosLeaf (NodeS l r)
      GoRight : {l, r : BinTreeShape} -> BinTreePosLeaf r -> BinTreePosLeaf (NodeS l r)

    %runElab deriveIndexed "BinTreePosLeaf" [Eq, Show]


namespace ApplicativeRoseTree
  public export
  data RoseTreeShape : (c : ContA) -> Type where
    LeafS : RoseTreeShape c
    NodeS : (GetC c) `fullOf` (RoseTreeShape c) -> RoseTreeShape c

  -- %runElab derive "RoseTreeShape" [Eq, Show]

  public export
  numLeaves : Foldable (Ext (GetC c)) => RoseTreeShape c -> Nat
  numLeaves LeafS = 1
  numLeaves (NodeS exts) = sum (numLeaves <$> exts)

  public export
  numNodes : Foldable (Ext (GetC c)) => RoseTreeShape c -> Nat
  numNodes LeafS = 0
  numNodes (NodeS exts) = 1 + sum (numNodes <$> exts)

  namespace NodesAndLeaves
    ||| Positions corresponding to both nodes and leaves within a RoseTreeShape
    public export
    data RoseTreePos : (c : ContA) -> (t : RoseTreeShape c) -> Type where
      DoneLeaf : RoseTreePos c LeafS
      DoneNode : {ts : (GetC c) `fullOf` (RoseTreeShape c)} ->
        RoseTreePos c (NodeS ts)
      SubTree : {ts : (GetC c) `fullOf` (RoseTreeShape c)} ->
        (ps : c.pos (shapeExt ts)) -> -- position in a given list
        RoseTreePos c (indexCont ts ps) -> -- position in the shape of RoseTree at a location specified by ps
        RoseTreePos c (NodeS ts)
  
  namespace Nodes
    public export
    data RoseTreePosNode : (c : ContA) -> (t : RoseTreeShape c) -> Type where
      DoneNode : {ts : (GetC c) `fullOf` (RoseTreeShape c)} ->
        RoseTreePosNode c (NodeS ts)
      SubTree : {ts : (GetC c) `fullOf` (RoseTreeShape c)} ->
        (ps : c.pos (shapeExt ts)) -> -- position in a given list
        RoseTreePosNode c (indexCont ts ps) -> -- position in the sub-tree at the above defined position
        RoseTreePosNode c (NodeS ts)

  namespace Leaves
    public export
    data RoseTreePosLeaf : (c : ContA) -> (t : RoseTreeShape c) -> Type where
      DoneLeaf : RoseTreePosLeaf c LeafS
      SubTree : {ts : (GetC c) `fullOf` (RoseTreeShape c)} ->
        (ps : c.pos (shapeExt ts)) -> -- position in a given list
        RoseTreePosLeaf c (indexCont ts ps) -> -- position in the sub-tree at the above defined position
        RoseTreePosLeaf c (NodeS ts)
    


{-
old rose tree implementation
namespace RoseTrees
  ||| Rose tree, a tree with a variable number of children.
  ||| This can likely be generalised to other Applicatives than List
  public export
  data RoseTreeShape : Type where
    LeafS : RoseTreeShape
    NodeS : List RoseTreeShape -> RoseTreeShape

  %runElab derive "RoseTreeShape" [Eq, Show]
  %name RoseTreeShape t, t1, t2, t3

  public export
  numLeaves : RoseTreeShape -> Nat
  numLeaves LeafS = 1
  numLeaves (NodeS ts) = sum (numLeaves <$> ts)
  
  public export
  numNodes : RoseTreeShape -> Nat
  numNodes LeafS = 0
  numNodes (NodeS ts) = 1 + sum (numNodes <$> ts)

  namespace NodesAndLeaves
    ||| Positions corresponding to both nodes and leaves within a RoseTreeShape
    public export
    data RoseTreePos : (t : RoseTreeShape) -> Type where
      DoneLeaf : RoseTreePos LeafS
      DoneNode : {ts : List RoseTreeShape} -> RoseTreePos (NodeS ts)
      SubTree : {ts : List RoseTreeShape} ->
        (i : Fin (length ts)) -> -- which subtree
        RoseTreePos (index' ts i) -> -- position in that subtree
        RoseTreePos (NodeS ts)

    -- For some reason the line below breaks?
    -- %runElab deriveIndexed "RoseTreePos" [Eq, Show]

  namespace Nodes
    ||| Positions corresponding to internal nodes within a RoseTreeNode shape.
    public export
    data RoseTreePosNode : (t : RoseTreeShape) -> Type where
      Done : {ts : List RoseTreeShape} -> RoseTreePosNode (NodeS ts)
      SubTree : {ts : List RoseTreeShape} ->
        (i : Fin (length ts)) -> -- which subtree
        RoseTreePosNode (index' ts i) -> -- position in that subtree
        RoseTreePosNode (NodeS ts)

    -- %runElab deriveIndexed "RoseTreePosNode" [Eq, Show]
  
  namespace Leaves
    ||| Positions corresponding to leaves within a RoseTreeLeaf shape.
    public export
    data RoseTreePosLeaf : (t : RoseTreeShape) -> Type where
      Done : RoseTreePosLeaf LeafS
      SubTree : {ts : List RoseTreeShape} ->
        (i : Fin (length ts)) -> -- which subtree
        RoseTreePosLeaf (index' ts i) -> -- position in that subtree
        RoseTreePosLeaf (NodeS ts)
  
    -- %runElab deriveIndexed "RoseTreePosLeaf" [Eq, Show]
 -}
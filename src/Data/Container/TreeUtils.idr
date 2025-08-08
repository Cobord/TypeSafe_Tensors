module Data.Container.TreeUtils

import Language.Reflection
import Derive.Prelude

import Data.Container.SubTerm

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
  data BTreeShape : Type where
    LeafS : BTreeShape
    NodeS : BTreeShape -> BTreeShape -> BTreeShape

  %runElab derive "BTreeShape" [Eq, Show]
  %name BTreeShape b, b1, b2, b3, b4, b5

  public export
  numLeaves : BTreeShape -> Nat
  numLeaves LeafS = 1
  numLeaves (NodeS lt rt) = numLeaves lt + numLeaves rt
  
  public export
  numNodes : BTreeShape -> Nat
  numNodes LeafS = 0
  numNodes (NodeS lt rt) = numNodes lt + (1 + numNodes rt)
  
  namespace NodesAndLeaves
    ||| Positions corresponding to both nodes and leaves within a BTreeShape
    public export
    data BTreePos : (b : BTreeShape) -> Type where
      DoneLeaf : BTreePos LeafS
      DoneNode : {l, r : BTreeShape} -> BTreePos (NodeS l r)
      GoLeft : {l, r : BTreeShape} -> BTreePos l -> BTreePos (NodeS l r)
      GoRight : {l, r : BTreeShape} -> BTreePos r -> BTreePos (NodeS l r)

    %runElab deriveIndexed "BTreePos" [Eq, Show]

  ||| Check if a term is a subterm of another term
  ||| t1 < t2 means that t2 > t1
  public export
  MOrd (BTreePos b) where
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



  Tr : BTreeShape
  Tr = NodeS (NodeS LeafS LeafS) LeafS
    
  Path1 : BTreePos Tr
  Path1 = GoLeft DoneNode

  Path2 : BTreePos Tr
  Path2 = GoLeft (GoLeft DoneLeaf)

  Path3 : BTreePos Tr
  Path3 = GoRight DoneLeaf

  fh : (mcompare Path1 Path2) = Just LT
  fh = ?asdf
  
  namespace Nodes
    ||| Positions corresponding to nodes within a BTreeNode shape.
    public export
    data BTreePosNode : (b : BTreeShape) -> Type where
      Done : {l, r : BTreeShape} -> BTreePosNode (NodeS l r)
      GoLeft  : {l, r : BTreeShape} -> BTreePosNode l -> BTreePosNode (NodeS l r)
      GoRight  : {l, r : BTreeShape} -> BTreePosNode r -> BTreePosNode (NodeS l r)

    %runElab deriveIndexed "BTreePosNode" [Eq, Show]
  
  namespace Leaves
    ||| Positions corresponding to leaves within a BTreeShape 
    public export
    data BTreePosLeaf : (b : BTreeShape) -> Type where
      Done : BTreePosLeaf LeafS
      GoLeft : {l, r : BTreeShape} -> BTreePosLeaf l -> BTreePosLeaf (NodeS l r)
      GoRight : {l, r : BTreeShape} -> BTreePosLeaf r -> BTreePosLeaf (NodeS l r)

    %runElab deriveIndexed "BTreePosLeaf" [Eq, Show]


namespace RoseTrees
  ||| Rose tree, a tree with a variable number of children.
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
      Here : {t : RoseTreeShape} -> {ts : List RoseTreeShape} ->
        RoseTreePos t ->
        RoseTreePos (NodeS (t :: ts))
      There : {t : RoseTreeShape} -> {ts : List RoseTreeShape} ->
        RoseTreePos (NodeS ts) ->
        RoseTreePos (NodeS (t :: ts))

    %runElab deriveIndexed "RoseTreePos" [Eq, Show]

  namespace Nodes
    ||| Positions corresponding to internal nodes within a RoseTreeNode shape.
    public export
    data RoseTreePosNode : (t : RoseTreeShape) -> Type where
      Done : {ts : List RoseTreeShape} -> RoseTreePosNode (NodeS ts)
      Here : {t : RoseTreeShape} -> {ts : List RoseTreeShape} ->
        RoseTreePosNode t ->
        RoseTreePosNode (NodeS (t :: ts))
      There : {t : RoseTreeShape} -> {ts : List RoseTreeShape} ->
        RoseTreePosNode (NodeS ts) ->
        RoseTreePosNode (NodeS (t :: ts))

    %runElab deriveIndexed "RoseTreePosNode" [Eq, Show]
  
  namespace Leaves
    ||| Positions corresponding to leaves within a RoseTreeLeaf shape.
    public export
    data RoseTreePosLeaf : (t : RoseTreeShape) -> Type where
      Done : RoseTreePosLeaf LeafS
      Here : {t : RoseTreeShape} -> {ts : List RoseTreeShape} ->
        RoseTreePosLeaf t ->
        RoseTreePosLeaf (NodeS (t :: ts))
      There : {t : RoseTreeShape} -> {ts : List RoseTreeShape} ->
        RoseTreePosLeaf (NodeS ts) ->
        RoseTreePosLeaf (NodeS (t :: ts))
  
    %runElab deriveIndexed "RoseTreePosLeaf" [Eq, Show]
  
module Data.Container.Applicative.Instances

import Data.Fin
import Data.DPair

import Data.Container.Object.Definition
import Data.Container.Object.Instances
import Data.Container.Concrete.Definition
import Data.Container.Concrete.Instances
import Data.Container.Applicative.Definition

import Data.Tree
import Misc

%hide Prelude.(<|)

-- Can now implement by converting to and from concrete instances?
namespace ListApplicative
  ||| This arises out of the Prelude.Types List applicative 
  ||| Effectively it behaves like a cartesian product
  public export 
  [cartProdInstance] Applicative List' where
    pure = fromList . pure
    fs <*> vs = fromList $ toList fs <*> toList vs

  public export
  listZip' : List' a -> List' b -> List' (a, b)
  listZip' l1 l2 = fromList $ listZip (toList l1) (toList l2)

  ||| This another List applicative, behaving like the usual zip one
  ||| It appears that List doesn't have the concrete Zippable instance written
  ||| Only one in Data.Zippable that follows from Applicative, which isn't the one we want
  ||| This is the one we use by default, as it's more useful for linear algebra
  public export
  Applicative List' where
    pure = fromList . pure
    fs <*> vs = fromList $ uncurry ($) <$> listZip (toList fs) (toList vs)


namespace BinTreeLeafApplicative
  public export
  liftA2BBinTreeLeaf' : BinTreeLeaf' a -> BinTreeLeaf' b -> BinTreeLeaf' (a, b)
  liftA2BBinTreeLeaf' (LeafS <| v) (LeafS <| v') = LeafS <| (\x => (v x, v' x))
  liftA2BBinTreeLeaf' (LeafS <| v) (NodeS l' r' <| v') =
    NodeS l' r' <| \case
        GoLeft posL' => (v Done, v' (GoLeft posL'))
        GoRight posR' => (v Done, v' (GoRight posR'))
  liftA2BBinTreeLeaf' (NodeS l r <| v) (LeafS <| v') =
    NodeS l r <| \case
        GoLeft posL => (v (GoLeft posL), v' Done)
        GoRight posR => (v (GoRight posR), v' Done)
  liftA2BBinTreeLeaf' (NodeS l r <| v) (NodeS l' r' <| v') =
    let (ls <| fl) = liftA2BBinTreeLeaf' (l <| v . GoLeft) (l' <| v' . GoLeft)
        (rs <| fr) = liftA2BBinTreeLeaf' (r <| v . GoRight) (r' <| v' . GoRight)
    in (NodeS ls rs <| \case
          GoLeft posL => fl posL
          GoRight posR => fr posR)

  public export
  Applicative BinTreeLeaf' where
    pure a = LeafS <| \_ => a
    fs <*> vs = uncurry ($) <$> liftA2BBinTreeLeaf' fs vs 


namespace BinTreeNodeApplicative
  -- TODO missing Eq instance for trees

  impossibleCase : BinTreePosNode LeafS -> (a, b)
  impossibleCase Done impossible
  impossibleCase (GoLeft x) impossible
  impossibleCase (GoRight x) impossible

  ||| Combine two BinTreeNode' structures, pairing values at corresponding nodes.
  ||| The resulting shape is the intersection of the input shapes.
  public export
  liftA2BinTreeNode' : BinTreeNode' a -> BinTreeNode' b -> BinTreeNode' (a, b)
  liftA2BinTreeNode' (NodeS l1 r1 <| f1) (NodeS l2 r2 <| f2) =
    let (ls <| fl) = liftA2BinTreeNode' (l1 <| f1 . GoLeft) (l2 <| f2 . GoLeft)
        (rs <| fr) = liftA2BinTreeNode' (r1 <| f1 . GoRight) (r2 <| f2 . GoRight)

        resultFunc : BinTreePosNode (NodeS ls rs) -> (a, b)
        resultFunc Done = (f1 Done, f2 Done)
        resultFunc (GoLeft posL) = fl posL
        resultFunc (GoRight posR) = fr posR
    in (NodeS ls rs <| resultFunc)
  liftA2BinTreeNode' _ _ = LeafS <| impossibleCase

  public export
  Applicative BinTreeNode' where
    pure a = NodeS LeafS LeafS <| \_ => a
    fs <*> vs = uncurry ($) <$> liftA2BinTreeNode' fs vs 



namespace BinTreeApplicative
  public export
  liftA2BinTree' : BinTree' a -> BinTree' b -> BinTree' (a, b)
  liftA2BinTree' (LeafS <| i1) (LeafS <| i2) = LeafS <| \pos => (i1 pos, i2 pos)
  liftA2BinTree' (LeafS <| i1) ((NodeS lt2 rt2) <| i2) = NodeS lt2 rt2 <| \case
    DoneNode => (i1 DoneLeaf, i2 DoneNode)
    GoLeft posL => (i1 DoneLeaf, i2 (GoLeft posL)) 
    GoRight posR => (i1 DoneLeaf, i2 (GoRight posR))
  liftA2BinTree' ((NodeS lt1 rt1) <| i1) (LeafS <| i2) = NodeS lt1 rt1 <| \case
    DoneNode => (i1 DoneNode, i2 DoneLeaf)
    GoLeft posL => (i1 (GoLeft posL), i2 DoneLeaf)
    GoRight posR => (i1 (GoRight posR), i2 DoneLeaf)
  liftA2BinTree' ((NodeS lt1 rt1) <| i1) ((NodeS lt2 rt2) <| i2) =
    let (ls <| fl) = liftA2BinTree' (lt1 <| i1 . GoLeft) (lt2 <| i2 . GoLeft)
        (rs <| fr) = liftA2BinTree' (rt1 <| i1 . GoRight) (rt2 <| i2 . GoRight)
    in NodeS ls rs <| \case
        DoneNode => (i1 DoneNode, i2 DoneNode)
        GoLeft posL => fl posL
        GoRight posR => fr posR
  -- Is the above correct? I think so

  public export
  Applicative BinTree' where
    pure a = LeafS <| \_ => a
    fs <*> vs = uncurry ($) <$> liftA2BinTree' fs vs



namespace ApplicativeInstances
  ||| Container with a single thing
  public export
  Scalar : ContA
  Scalar = (#) Scalar
  
  ||| Product
  public export
  Pair : ContA
  Pair = (#) Pair

  -- TODO applicatives for these commented out types?
  -- ||| Coproduct
  -- public export
  -- Either : ContA
  -- Either = (#) Either

  -- ||| +1  
  -- public export
  -- Maybe : ContA
  -- Maybe = (#) Maybe
  
  public export
  List : ContA
  List = (#) List
  
  ||| Container of n things 
  ||| Every natural number n corresponds to a Vect n, which is applicative
  ||| Used in cubical tensors whose shapes are defined by lists of natural numbers
  public export
  Vect : Nat -> ContA
  Vect n = (#) (Vect n)

  ||| Container of an infinite number of things
  public export
  Stream : ContA
  Stream = (#) Stream

  ||| Binary trees with data stored at both nodes and leaves
  public export
  BinTree : ContA
  BinTree = (#) BinTree
  
  ||| Binary trees with data stored at nodes
  public export
  BinTreeNode : ContA
  BinTreeNode = (#) BinTreeNode
  
  ||| Binary trees with data stored at leaves
  public export
  BinTreeLeaf : ContA
  BinTreeLeaf = (#) BinTreeLeaf

  ||| Generalisation of Rose trees with a container
  ||| of subtrees (container whose extension is applicative)
  ||| instead of a list of a subtrees
  public export
  ApplicativeRoseTree : ContA -> Cont
  ApplicativeRoseTree c = (t : RoseTreeShape c) !> RoseTreePos c t

  ||| Same as above, but with data stored at nodes
  public export
  ApplicativeRoseTreeNode : ContA -> Cont
  ApplicativeRoseTreeNode c = (t : RoseTreeShape c) !> RoseTreePosNode c t

  ||| Same as above, but with data stored at leaf
  public export
  ApplicativeRoseTreeLeaf : ContA -> Cont
  ApplicativeRoseTreeLeaf c = (t : RoseTreeShape c) !> RoseTreePosNode c t


  ||| Rose tree here means ApplicativeRoseTree List
  namespace ContDefs
    ||| Rose trees with data stored at both nodes and leaves
    public export
    RoseTree : Cont
    RoseTree = ApplicativeRoseTree List
  
    ||| Rose trees with data stored at nodes
    public export
    RoseTreeNode : Cont
    RoseTreeNode = ApplicativeRoseTreeNode List
  
    ||| Rose trees with data stored at leaves
    public export
    RoseTreeLeaf : Cont
    RoseTreeLeaf = ApplicativeRoseTreeLeaf List


namespace ExtensionsOfApplicativeExamples
  ||| Isomorphic to Data.Tree.ApplicativeRoseTree (TODO)
  public export
  ApplicativeRoseTree' : (c : ContA) -> Type -> Type
  ApplicativeRoseTree' c = Ext (ApplicativeRoseTree c)

  public export
  ApplicativeRoseTreeNode' : (c : ContA) -> Type -> Type
  ApplicativeRoseTreeNode' c = Ext (ApplicativeRoseTreeNode c)

  public export
  ApplicativeRoseTreeLeaf' : (c : ContA) -> Type -> Type
  ApplicativeRoseTreeLeaf' c = Ext (ApplicativeRoseTreeLeaf c)


  ||| Isomorphic to Data.Tree.RoseTree
  public export
  RoseTree' : Type -> Type
  RoseTree' = Ext RoseTree

  ||| Isomorphic to Data.Tree.RoseTreeNode (TODO)
  public export
  RoseTreeNode' : Type -> Type
  RoseTreeNode' = Ext RoseTreeNode

  ||| Isomorphic to Data.Tree.RoseTreeLeaf (TODO)
  public export
  RoseTreeLeaf' : Type -> Type
  RoseTreeLeaf' = Ext RoseTreeLeaf


  -- TODO
  public export
  Applicative (Ext (ApplicativeRoseTree c)) where
    pure a = ?one
    fs <*> xs = ?two

  public export
  ApplicativeRoseTree : ContA -> ContA
  ApplicativeRoseTree c = (#) (ApplicativeRoseTree c)



namespace ConversionFunctions
  public export
  fromRoseTreeSame : RoseTreeSame a -> RoseTree' a
  fromRoseTreeSame (Leaf a) = LeafS <| \_ => a
  fromRoseTreeSame (Node a rts) =
    let t = fromRoseTreeSame <$> fromList rts
    in NodeS (shapeExt <$> t) <| \case
      DoneNode => a
      SubTree ps posSt =>
        let rw1 : (shapeExt t = shapeExt (shapeExt <$> t)) := sym (mapShapeExt t)
            rw2 : (shapeExt (indexCont t (rewrite sym (mapShapeExt {f=shapeExt} t) in ps)) = indexCont (shapeExt <$> t) ps) := mapIndexCont {c=List} {f=shapeExt} t ps
        in indexCont
        (indexCont t (rewrite rw1 in ps))
        (rewrite rw2 in posSt)
        -- for some reason all the explicit type annotations above are needed
        -- to convince the typechecker

  public export
  toRoseTreeSame : RoseTree' a -> RoseTreeSame a
  toRoseTreeSame (LeafS <| contentAt) = Leaf (contentAt DoneLeaf)
  toRoseTreeSame (NodeS (len <| content) <| contentAt)
    = Node (contentAt DoneNode)
           (toList $ toRoseTreeSame 
                  <$> (\i => content i <| contentAt . SubTree i)
                  <$> positionsCont)


public export
FromConcrete RoseTree where
  concreteType = RoseTreeSame
  concreteFunctor = %search
  fromConcreteTy = fromRoseTreeSame
  toConcreteTy = toRoseTreeSame

namespace RoseTreeInstances
  -- TODO this should be superseeded by the general applicative instance above?
  public export
  liftA2RoseTree' : RoseTree' a -> RoseTree' b -> RoseTree' (a, b)
  liftA2RoseTree' t1 t2 = fromRoseTreeSame $
    liftA2RoseTreeSame (toRoseTreeSame t1) (toRoseTreeSame t2)

  public export
  Applicative RoseTree' where
    pure a = LeafS <| \_ => a
    fs <*> vs = uncurry ($) <$> liftA2RoseTree' fs vs
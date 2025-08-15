module Data.Container.Applicative.Instances

import Data.Fin
import Data.DPair

import Data.Container.Definition
import Data.Container.Instances
import Data.Container.Applicative.Definition
import Data.Tree
import Misc

%hide Prelude.(<|)


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

  namespace ContDefs
    ||| Rose trees with data stored at both nodes and leaves
    public export
    RoseTree : Cont
    RoseTree = (t : RoseTreeShape List) !> RoseTreePos List t
  
    ||| Rose trees with data stored at nodes
    public export
    RoseTreeNode : Cont
    RoseTreeNode = (t : RoseTreeShape List) !> RoseTreePosNode List t
  
    ||| Rose trees with data stored at leaves
    public export
    RoseTreeLeaf : Cont
    RoseTreeLeaf = (t : RoseTreeShape List) !> RoseTreePosLeaf List t

  -- TODO
  public export
  Applicative (Ext (ApplicativeRoseTree c)) where
    pure a = ?one
    fs <*> xs = ?two

  public export
  ApplicativeRoseTree : ContA -> ContA
  ApplicativeRoseTree c = (#) (ApplicativeRoseTree c)


namespace ExtensionsOfApplicativeExamples
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
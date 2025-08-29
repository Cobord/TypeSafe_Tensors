module Data.Container.Applicative.Instances

import Data.Fin
import Data.DPair

import Data.Container.Object.Definition
import Data.Container.Object.Instances
import Data.Container.Extension.Definition
import Data.Container.Extension.Instances
import Data.Container.Concrete.Definition
import Data.Container.Concrete.Instances
import Data.Container.Applicative.Definition

import Misc

%hide Prelude.(<|)

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
  liftA2BBinTreeLeaf' t1 t2 = fromBinTreeLeaf $
    liftA2BinTreeLeaf (toBinTreeLeaf t1) (toBinTreeLeaf t2)

  public export
  Applicative BinTreeLeaf' where
    pure a = fromBinTreeLeaf (Leaf a)
    fs <*> vs = uncurry ($) <$> liftA2BBinTreeLeaf' fs vs 


-- no applicative instance for BinTreeNode
-- there is one for infinite trees

namespace BinTreeApplicative
  public export
  liftA2BinTree' : BinTree' a -> BinTree' b -> BinTree' (a, b)
  liftA2BinTree' t1 t2 = fromBinTreeSame $
    liftA2BinTreeSame (toBinTreeSame t1) (toBinTreeSame t2)

  public export
  Applicative BinTree' where
    pure a = fromBinTreeSame (Leaf a)
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
  
  ||| Binary trees with data stored at leaves
  public export
  BinTreeLeaf : ContA
  BinTreeLeaf = (#) BinTreeLeaf

  public export
  TensorA : List ContA -> Cont
  TensorA cs = Tensor (GetC <$> cs)
  
  public export
  composeExtensionsA : List ContA -> Type -> Type
  composeExtensionsA cs = composeExtensions (GetC <$> cs)




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
            rw2 : (shapeExt (index t (rewrite sym (mapShapeExt {f=shapeExt} t) in ps)) = index (shapeExt <$> t) ps) := mapIndexCont {c=List} {f=shapeExt} t ps
        in index
        (index t (rewrite rw1 in ps))
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



namespace TensorApplicativeInstances
  public export
  tensorReplicate : {shape : List Cont} ->
    (allAppl : AllApplicative shape) =>
    (x : a) -> Tensor' shape a
  tensorReplicate {shape = []} x = toScalar x
  tensorReplicate {shape = (c :: cs)} {allAppl = Cons @{fst} @{rest}} x
    = fromExtensionComposition {shape=(c::cs)}
      (pure (toExtensionComposition (tensorReplicate x)))

  public export
  liftA2Tensor : {shape : List Cont} ->
    (allAppl : AllApplicative shape) =>
    Tensor' shape a -> Tensor' shape b -> Tensor' shape (a, b)
  liftA2Tensor {shape = []} t t' = () <| \() => (index t (), index t' ())
  liftA2Tensor {shape = (c :: cs)} {allAppl = Cons @{fr} @{rst} } t t'
    = embedExt $ uncurry liftA2Tensor <$> liftA2 (extractExt t) (extractExt t')

  public export
  {c : Cont} -> (allAppl : AllApplicative [c]) =>
  Applicative (Tensor' [c]) where
    pure = tensorReplicate {allAppl = allAppl}
    fs <*> xs = uncurry ($) <$> liftA2Tensor {allAppl = allAppl} fs xs

  public export
  {c, d : Cont} -> (allAppl : AllApplicative [c, d]) =>
  Applicative (Tensor' [c, d]) where
    pure = tensorReplicate {allAppl = allAppl}
    fs <*> xs = uncurry ($) <$> liftA2Tensor {allAppl = allAppl} fs xs

  public export
  {c, d, e : Cont} -> (allAppl : AllApplicative [c, d, e]) =>
  Applicative (Tensor' [c, d, e]) where
    pure = tensorReplicate {allAppl = allAppl}
    fs <*> xs = uncurry ($) <$> liftA2Tensor {allAppl = allAppl} fs xs

  public export
  {c, d, e, f : Cont} -> (allAppl : AllApplicative [c, d, e, f]) =>
  Applicative (Tensor' [c, d, e, f]) where
    pure = tensorReplicate {allAppl = allAppl}
    fs <*> xs = uncurry ($) <$> liftA2Tensor {allAppl = allAppl} fs xs

  public export
  {c, d, e, f, g : Cont} -> (allAppl : AllApplicative [c, d, e, f, g]) =>
  Applicative (Tensor' [c, d, e, f, g]) where
    pure = tensorReplicate {allAppl = allAppl}
    fs <*> xs = uncurry ($) <$> liftA2Tensor {allAppl = allAppl} fs xs
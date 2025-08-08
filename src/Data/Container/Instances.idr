module Data.Container.Instances

import Data.Fin
import Data.Vect


import Data.Container.Definition
import Data.Functor.Naperian
import Misc
import Data.Tree
import Data.Algebra
import public Data.Container.TreeUtils -- rexport all the stuff inside


%hide Data.Vect.fromList


||| Examples
namespace MainContainerExamples
  ||| Container with a single thing
  public export
  Scalar : Cont
  Scalar = (_ : Unit) !> Unit

  ||| Product
  public export
  Pair : Cont
  Pair = (_ : Unit) !> Bool

  ||| Coproduct
  public export
  Either : Cont
  Either = (_ : Bool) !> Unit

  ||| +1  
  public export
  Maybe : Cont
  Maybe = (b : Bool) !> (if b then Unit else Void)

  ||| List, container with an unknown number of elements 
  public export
  List : Cont
  List = (n : Nat) !> Fin n
  
  ||| Vect, container of a known number of things 
  public export
  Vect : Nat -> Cont
  Vect n = (_ : Unit) !> Fin n

  ||| Container of an infinite number of things
  public export
  Stream : Cont
  Stream = (_ : Unit) !> Nat

  ||| Binary trees with data stored at both nodes and leaves
  public export
  BTree : Cont
  BTree = (b : BTreeShape) !> BTreePos b
  
  ||| Binary trees with data stored at nodes
  public export
  BTreeNode : Cont
  BTreeNode = (b : BTreeShape) !> BTreePosNode b
  
  ||| Binary trees with data stored at leaves
  public export
  BTreeLeaf : Cont
  BTreeLeaf = (b : BTreeShape) !> BTreePosLeaf b

  ||| Rose trees with data stored at both nodes and leaves
  public export
  RoseTree : Cont
  RoseTree = (t : RoseTreeShape) !> RoseTreePos t

  ||| Rose trees with data stored at nodes
  public export
  RoseTreeNode : Cont
  RoseTreeNode = (t : RoseTreeShape) !> RoseTreePosNode t

  ||| Rose trees with data stored at leaves
  public export
  RoseTreeLeaf : Cont
  RoseTreeLeaf = (t : RoseTreeShape) !> RoseTreePosLeaf t

  ||| Every lens gives rise to a container
  ||| The set of shapes is the lens itself
  ||| The set of positions is the inputs to the lens
  public export
  InternalLens : Cont -> Cont -> Cont
  InternalLens c d
    = (f : ((x : c.shp) -> (y : d.shp ** d.pos y -> c.pos x)))
      !> (xx : c.shp ** d.pos (fst (f xx)))

namespace ExtensionsOfMainContainerExamples
  ||| Isomorphic to the Identity
  public export
  Scalar' : Type -> Type
  Scalar' = Ext Scalar

  ||| Isomorphic to Pair
  public export
  Pair' : Type -> Type
  Pair' = Ext Pair
  
  ||| Isomorphic to Either
  public export
  Either' : Type -> Type
  Either' = Ext Either

  ||| Isomorphic to Maybe
  public export
  Maybe' : Type -> Type
  Maybe' = Ext Maybe
  
  ||| Isomorphic to List
  public export
  List' : Type -> Type
  List' = Ext List

  ||| Isomorphic to Vect
  public export
  Vect' : (n : Nat) -> Type -> Type
  Vect' n x = (Vect n) `fullOf` x

  ||| Isomorphic to Stream
  public export
  Stream' : Type -> Type
  Stream' = Ext Stream

  ||| Isomorphic to Data.Tree.BTreeSame
  public export
  BTree' : Type -> Type
  BTree' = Ext BTree

  ||| Isomorphic to Data.Tree.BTreeNode
  public export
  BTreeNode' : Type -> Type
  BTreeNode' = Ext BTreeNode
  
  ||| Isomorphic to Data.Tree.BTreeLeaf
  public export
  BTreeLeaf' : Type -> Type
  BTreeLeaf' = Ext BTreeLeaf

  ||| Isomorphic to Data.Tree.RoseTree (TODO)
  public export
  RoseTree' : Type -> Type
  RoseTree' = Ext RoseTree

  ||| Isomorphic to RoseTreeNode
  public export
  RoseTreeNode' : Type -> Type
  RoseTreeNode' = Ext RoseTreeNode

  public export
  RoseTreeLeaf' : Type -> Type
  RoseTreeLeaf' = Ext RoseTreeLeaf

namespace ConversionFunctions
  public export
  fromIdentity : a -> Scalar' a
  fromIdentity a = () <| (\_ => a)

  public export
  toIdentity : Scalar' a -> a
  toIdentity (() <| f) = f ()

  public export
  fromList : List x -> List' x
  fromList [] = (0 <| absurd)
  fromList (x :: xs) = let (l <| c) = fromList xs
                       in (S l <| addBeginning x c)

  public export
  toList : List' x -> List x
  toList (0 <| _) = []
  toList ((S k) <| ind) = let (x, c) = removeBeginning ind
                          in x :: toList (k <| c)
  
  public export
  fromVect : Vect n x -> Vect' n x
  fromVect v = () <| \i => index i v
  
  public export
  toVect : {n : Nat} -> Vect' n x -> Vect n x
  toVect (_ <| indexCont) = vectTabulate indexCont
  
  
  public export
  fromTreeHelper : BTreePosNode LeafS -> a
  fromTreeHelper Done impossible
  fromTreeHelper (GoLeft x) impossible
  fromTreeHelper (GoRight x) impossible
  
  public export
  fromBTreeNode : BTreeNode a -> BTreeNode' a
  fromBTreeNode (Leaf ()) = (LeafS <| fromTreeHelper)
  fromBTreeNode (Node node leftTree rightTree)
    = let (lts <| ltc) = fromBTreeNode leftTree
          (rts <| rtc) = fromBTreeNode rightTree
      in (NodeS lts rts <| \pos =>
            case pos of
              Done => node
              GoLeft posL => ltc posL
              GoRight posR => rtc posR)

  public export
  toBTreeNode : BTreeNode' a -> BTreeNode a
  toBTreeNode (LeafS <| indexCont) = Leaf ()
  toBTreeNode (NodeS lt rt <| indexCont) = 
    Node (indexCont Done)
         (toBTreeNode (lt <| indexCont . GoLeft))
         (toBTreeNode (rt <| indexCont . GoRight))
  
  public export
  fromBTreeLeaf : BTreeLeaf a -> BTreeLeaf' a
  fromBTreeLeaf (Leaf leaf) = LeafS <| \_ => leaf
  fromBTreeLeaf (Node node lt rt) =
    let (shL <| fnL) = fromBTreeLeaf lt
        (shR <| fnR) = fromBTreeLeaf rt
    in NodeS shL shR <| \case
          GoLeft posL => fnL posL
          GoRight posR => fnR posR

  public export
  toBTreeLeaf : BTreeLeaf' a -> BTreeLeaf a
  toBTreeLeaf (LeafS <| content) = Leaf (content Done)
  toBTreeLeaf (NodeS l r <| content) =
    Node' (toBTreeLeaf (l <| content . GoLeft))
          (toBTreeLeaf (r <| content . GoRight))


public export
interface FromConcrete (cont : Cont) where
  constructor MkConcrete
  concreteType : Type -> Type
  concreteFunctor : Functor (concreteType)
  fromConcreteTy : concreteType a -> Ext cont a
  toConcreteTy : Ext cont a -> concreteType a

-- public export
-- fromConcreteMap : {cont1, cont2 : Cont} ->
--   (fc1 : FromConcrete cont1) => (fc2 : FromConcrete cont2) =>
--   (concreteType @{fc1} a -> concreteType @{fc2} b) ->
--   cont1 `fullOf` a -> cont2 `fullOf` b
-- fromConcreteMap f = fromConcrete @{fc2} . f . toConcrete @{fc1}


Functor Basics.id where
  map = id

public export
FromConcrete Scalar where
  concreteType = id
  concreteFunctor = %search
  fromConcreteTy = fromIdentity
  toConcreteTy = toIdentity

public export
FromConcrete List where
  concreteType = List
  concreteFunctor = %search -- TODO how to find the result of the search and place it here directly?
  fromConcreteTy = fromList
  toConcreteTy = toList

public export
{n : Nat} -> FromConcrete (Vect n) where
  concreteType = Vect n
  concreteFunctor = %search
  fromConcreteTy = fromVect
  toConcreteTy = toVect

public export
FromConcrete BTreeNode where
  concreteType = BTreeNode
  concreteFunctor = %search
  fromConcreteTy = fromBTreeNode
  toConcreteTy = toBTreeNode

public export
FromConcrete BTreeLeaf where
  concreteType = BTreeLeaf
  concreteFunctor = %search
  fromConcreteTy = fromBTreeLeaf
  toConcreteTy = toBTreeLeaf

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

  ||| This arises out of the Prelude.Types List applicative 
  ||| Effectively it behaves like the outer product
  public export 
  [cartProd] Applicative List' where
    pure = fromList . pure
    fs <*> vs = fromList $ toList fs <*> toList vs

  public export
  listZip : List a -> List b -> List (a, b)
  listZip [] [] = []
  listZip [] (y :: ys) = []
  listZip (x :: xs) [] = []
  listZip (x :: xs) (y :: ys) = (x, y) :: listZip xs ys

  listZip' : List' a -> List' b -> List' (a, b)
  listZip' (sh1 <| ind1) (sh2 <| ind2) = minimum sh1 sh2 <| \p => ?vm

  ||| This another List applicative, behaving like the usual zip one
  ||| It appears that List doesn't have the concret Zippable instance written
  ||| Only one in Data.Zippable that follows from Applicative, which isn't the one we want
  public export
  Applicative List' where
    pure = fromList . pure
    fs <*> vs = fromList $ uncurry ($) <$> listZip (toList fs) (toList vs)


namespace BTreeInstances
  {- 
     a           b 
    / \         / \ 
   lt  rt     lt'  rt'
  -}
  ||| TODO finish implementation
  public export
  liftA2BTree' : BTree' a -> BTree' b -> BTree' (a, b)
  liftA2BTree' (LeafS <| i1) (LeafS <| i2) = LeafS <| \pos => (i1 pos, i2 pos)
  liftA2BTree' (LeafS <| i1) ((NodeS lt2 rt2) <| i2) = NodeS lt2 rt2 <| \case
    DoneNode => (i1 DoneLeaf, i2 DoneNode)
    GoLeft posL => (i1 DoneLeaf, i2 (GoLeft posL)) 
    GoRight posR => (i1 DoneLeaf, i2 (GoRight posR))
  liftA2BTree' ((NodeS lt1 rt1) <| i1) (LeafS <| i2) = NodeS lt1 rt1 <| \case
    DoneNode => (i1 DoneNode, i2 DoneLeaf)
    GoLeft posL => (i1 (GoLeft posL), i2 DoneLeaf)
    GoRight posR => (i1 (GoRight posR), i2 DoneLeaf)
  liftA2BTree' ((NodeS lt1 rt1) <| i1) ((NodeS lt2 rt2) <| i2) =
    let (ls <| fl) = liftA2BTree' (lt1 <| i1 . GoLeft) (lt2 <| i2 . GoLeft)
        (rs <| fr) = liftA2BTree' (rt1 <| i1 . GoRight) (rt2 <| i2 . GoRight)
    in NodeS ls rs <| \case
        DoneNode => (i1 DoneNode, i2 DoneNode)
        GoLeft posL => fl posL
        GoRight posR => fr posR
  -- Is the above correct? I think so

  public export
  Applicative BTree' where
    pure a = LeafS <| \_ => a
    fs <*> vs = uncurry ($) <$> liftA2BTree' fs vs


namespace BTreeLeafInstances
  public export
  showBTreeLeaf' : Show a => BTreeLeaf' a -> String
  showBTreeLeaf' (LeafS <| content) = "Leaf (" ++ show (content Done) ++ ")"
  showBTreeLeaf' ((NodeS l r) <| content) =
    let leftSubtree : BTreeLeaf' a = (l <| \posL => content (GoLeft posL))
        rightSubtree : BTreeLeaf' a = (r <| \posR => content (GoRight posR))
    in "Node (" ++ showBTreeLeaf' leftSubtree ++ ") (" ++ showBTreeLeaf' rightSubtree ++ ")"

  partial -- not partial but not sure how to convince Idris totality checker
  public export
  Show a => Show (BTreeLeaf' a) where
    show t = show (toBTreeLeaf t)

  public export
  Eq a => Eq (BTreeLeaf' a) where
    (LeafS <| v) == (LeafS <| v') = v Done == v' Done
    ((NodeS l r) <| v) == ((NodeS l' r') <| v') =
      (l == l') && (r == r') && ?vnm -- Assuming Eq BTreeShape is defined elsewhere
    _ == _ = False

  public export
  liftA2BBTreeLeaf' : BTreeLeaf' a -> BTreeLeaf' b -> BTreeLeaf' (a, b)
  liftA2BBTreeLeaf' (LeafS <| v) (LeafS <| v') = LeafS <| (\x => (v x, v' x))
  liftA2BBTreeLeaf' (LeafS <| v) (NodeS l' r' <| v') =
    NodeS l' r' <| \case
        GoLeft posL' => (v Done, v' (GoLeft posL'))
        GoRight posR' => (v Done, v' (GoRight posR'))
  liftA2BBTreeLeaf' (NodeS l r <| v) (LeafS <| v') =
    NodeS l r <| \case
        GoLeft posL => (v (GoLeft posL), v' Done)
        GoRight posR => (v (GoRight posR), v' Done)
  liftA2BBTreeLeaf' (NodeS l r <| v) (NodeS l' r' <| v') =
    let (ls <| fl) = liftA2BBTreeLeaf' (l <| v . GoLeft) (l' <| v' . GoLeft)
        (rs <| fr) = liftA2BBTreeLeaf' (r <| v . GoRight) (r' <| v' . GoRight)
    in (NodeS ls rs <| \case
          GoLeft posL => fl posL
          GoRight posR => fr posR)

  public export
  Applicative BTreeLeaf' where
    pure a = LeafS <| \_ => a
    fs <*> vs = uncurry ($) <$> liftA2BBTreeLeaf' fs vs 


  ||| Just summing up elements of the tree given by the Num a structure
  public export
  Num a => Algebra BTreeLeaf' a where
    reduce (LeafS <| v) = v Done
    reduce (NodeS l r <| v) =
      let leftSubtree = l <| v . GoLeft
          rightSubtree = r <| v . GoRight
      in reduce {f=BTreeLeaf'} leftSubtree +
         reduce {f=BTreeLeaf'} rightSubtree


namespace BTreeNodeInstances
  -- TODO missing Eq instance for trees

  impossibleCase : BTreePosNode LeafS -> (a, b)
  impossibleCase Done impossible
  impossibleCase (GoLeft x) impossible
  impossibleCase (GoRight x) impossible

  ||| Combine two BTreeNode' structures, pairing values at corresponding nodes.
  ||| The resulting shape is the intersection of the input shapes.
  public export
  liftA2BTreeNode' : BTreeNode' a -> BTreeNode' b -> BTreeNode' (a, b)
  liftA2BTreeNode' (NodeS l1 r1 <| f1) (NodeS l2 r2 <| f2) =
    let (ls <| fl) = liftA2BTreeNode' (l1 <| f1 . GoLeft) (l2 <| f2 . GoLeft)
        (rs <| fr) = liftA2BTreeNode' (r1 <| f1 . GoRight) (r2 <| f2 . GoRight)

        resultFunc : BTreePosNode (NodeS ls rs) -> (a, b)
        resultFunc Done = (f1 Done, f2 Done)
        resultFunc (GoLeft posL) = fl posL
        resultFunc (GoRight posR) = fr posR
    in (NodeS ls rs <| resultFunc)
  liftA2BTreeNode' _ _ = LeafS <| impossibleCase

  public export
  Applicative BTreeNode' where
    pure a = NodeS LeafS LeafS <| \_ => a
    fs <*> vs = uncurry ($) <$> liftA2BTreeNode' fs vs 

  public export
  Num a => Algebra BTreeNode' a where
    reduce (LeafS <| v) = fromInteger 0
    reduce (NodeS l r <| v) = v Done +
      reduce {f=BTreeNode'} (l <| v . GoLeft) +
      reduce {f=BTreeNode'} (r <| v . GoRight)
  
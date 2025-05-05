module Data.Container.Instances

import Data.Fin
import Data.Vect


import Data.Container.Definition
import Tensor.Naperian
import Misc
import Data.Tree
import Algebra
import Data.Rig
import Data.Container.TreeUtils


%hide Data.Vect.fromList


namespace MainContainerExamples
  ||| Examples
  public export
  PairCont : Cont
  PairCont = (_ : Unit) !> Bool
  
  public export
  VectCont : Nat -> Cont
  VectCont n = (_ : Unit) !> Fin n
  
  public export
  MaybeCont : Cont
  MaybeCont = (b : Bool) !> (if b then Unit else Void)
  
  public export
  ListCont : Cont
  ListCont = (n : Nat) !> (Fin n)

  public export
  StreamCont : Cont
  StreamCont = (_ : Unit) !> Nat
  
  ||| Trees with data stored at nodes
  public export
  BTreeNodeCont : Cont
  BTreeNodeCont = (b : BTreeShape) !> FinBTreeNode b
  
  ||| Trees with data stored at leaves
  public export
  BTreeLeafCont : Cont
  BTreeLeafCont = (b : BTreeShape) !> FinBTreeLeaf b


namespace ExtensionsOfMainContainerExamples
  ||| Isomorphic to Pair
  public export
  Pair' : Type -> Type
  Pair' = Ext PairCont
  
  ||| Isomorphic to Vect
  public export
  Vect' : (n : Nat) -> Type -> Type
  Vect' n x = (VectCont n) `fullOf` x
  
  ||| Isomorphic to Maybe
  public export
  Maybe' : Type -> Type
  Maybe' = Ext MaybeCont
  
  ||| Isomorphic to List
  public export
  List' : Type -> Type
  List' = Ext ListCont
  
  ||| Isomorphic to Trees with data at only nodes
  public export
  BTreeNode' : Type -> Type
  BTreeNode' = Ext BTreeNodeCont
  
  ||| Isomorphic to Trees with data only at leaves
  public export
  BTreeLeaf' : Type -> Type
  BTreeLeaf' = Ext BTreeLeafCont


-- public export
-- Functor (Vect' n) where
--   map f a = map {f=(Ext (VectCont n))} f a

-- public export
-- {n : Nat} -> Applicative (Vect' n) where
--   pure a = fromVect (pure a)
--   fs <*> vs = fromVect $ toVect fs <*> toVect vs 



namespace ConversionFunctions
  public export
  fromList : List x -> List' x
  fromList [] = (0 <| absurd)
  fromList (x :: xs) = let (l <| c) = fromList xs
                       in (S l <| addBeginning x c)
  
  
  public export
  fromVect : Vect n x -> Vect' n x
  fromVect v = () <| \i => index i v
  
  public export
  toVect : {n : Nat} -> Vect' n x -> Vect n x
  toVect (_ <| indexCont) = vectTabulate indexCont
  
  
  
  
  fromTreeHelper : FinBTreeNode LeafS -> a
  fromTreeHelper Root impossible
  fromTreeHelper (GoL x) impossible
  fromTreeHelper (GoR x) impossible
  
  public export
  fromBTreeNode : BTreeNode a -> BTreeNode' a
  fromBTreeNode (Leaf ()) = (LeafS <| fromTreeHelper)
  fromBTreeNode (Node node leftTree rightTree)
    = let (lts <| ltc) = fromBTreeNode leftTree
          (rts <| rtc) = fromBTreeNode rightTree
      in (NodeS lts rts <| \pos =>
            case pos of
              Root => node
              GoL posL => ltc posL
              GoR posR => rtc posR)
  
  public export
  fromBTreeLeaf : BTreeLeaf a -> BTreeLeaf' a
  fromBTreeLeaf (Leaf leaf) = LeafS <| \_ => leaf
  fromBTreeLeaf (Node node lt rt) =
    let (shL <| fnL) = fromBTreeLeaf lt
        (shR <| fnR) = fromBTreeLeaf rt
    in (NodeS shL shR <| \pos =>
          case pos of
            GoLLeaf posL => fnL posL
            GoRLeaf posR => fnR posR)

  public export
  toBTreeLeaf : BTreeLeaf' a -> BTreeLeaf a
  toBTreeLeaf (LeafS <| content) = Leaf (content AtLeaf)
  toBTreeLeaf ((NodeS l r) <| content) =
    Node' (toBTreeLeaf (l <| \posL => content (GoLLeaf posL)))
          (toBTreeLeaf (r <| \posR => content (GoRLeaf posR)))

namespace VectInstances
  public export
  {n : Nat} -> Eq x => Eq (Ext (VectCont n) x) where
    v == v' = (toVect v) == (toVect v')
 
  public export
  {n : Nat} -> Show x => Show (Ext (VectCont n) x) where
    show v = show (toVect v)

  public export
  {n : Nat} -> Foldable (Ext (VectCont n)) where
    foldr f z v = foldr f z (toVect v)
  
  public export
  {n : Nat} -> Applicative (Ext (VectCont n)) where
    pure a = fromVect $ pure a
    fs <*> vs = fromVect $ toVect fs <*> toVect vs

  public export
  {n : Nat} -> Rig a => Algebra (Ext (VectCont n)) a where
    reduce v = reduce (toVect v)

  -- TODO Naperian instance? Or is that covered by the one in Definiton.idr?


namespace BTreeLeafInstances

  showBTreeLeaf' : Show a => BTreeLeaf' a -> String
  showBTreeLeaf' (LeafS <| content) = "Leaf (" ++ show {ty=a} (content AtLeaf) ++ ")"
  showBTreeLeaf' ((NodeS l r) <| content) =
    let leftSubtree : BTreeLeaf' a = (l <| \posL => content (GoLLeaf posL))
        rightSubtree : BTreeLeaf' a = (r <| \posR => content (GoRLeaf posR))
    in "Node (" ++ showBTreeLeaf' leftSubtree ++ ") (" ++ showBTreeLeaf' rightSubtree ++ ")"

  partial -- not partial but not sure how to convince Idris totality checker
  public export
  Show a => Show (BTreeLeaf' a) where
    show t = show (toBTreeLeaf t)

  public export
  Eq a => Eq (BTreeLeaf' a) where
    (LeafS <| v) == (LeafS <| v') = v AtLeaf == v' AtLeaf
    ((NodeS l r) <| v) == ((NodeS l' r') <| v') =
      (l == l') && (r == r') && ?vnm -- Assuming Eq BTreeShape is defined elsewhere
    _ == _ = False

  public export
  liftA2BBTreeLeaf' : BTreeLeaf' a -> BTreeLeaf' b -> BTreeLeaf' (a, b)
  liftA2BBTreeLeaf' (LeafS <| v) (LeafS <| v') = LeafS <| (\x => (v x, v' x))
  liftA2BBTreeLeaf' (LeafS <| v) (NodeS l' r' <| v') =
    NodeS l' r' <| \pos =>
      case pos of
        GoLLeaf posL' => (v AtLeaf, v' (GoLLeaf posL'))
        GoRLeaf posR' => (v AtLeaf, v' (GoRLeaf posR'))
  liftA2BBTreeLeaf' (NodeS l r <| v) (LeafS <| v') =
    NodeS l r <| \pos =>
      case pos of
        GoLLeaf posL => (v (GoLLeaf posL), v' AtLeaf)
        GoRLeaf posR => (v (GoRLeaf posR), v' AtLeaf)
  liftA2BBTreeLeaf' (NodeS l r <| v) (NodeS l' r' <| v') =
    let (ls <| fl) = liftA2BBTreeLeaf' (l <| v . GoLLeaf) (l' <| v' . GoLLeaf)
        (rs <| fr) = liftA2BBTreeLeaf' (r <| v . GoRLeaf) (r' <| v' . GoRLeaf)
    in (NodeS ls rs <| \pos =>
         case pos of
           GoLLeaf posL => fl posL
           GoRLeaf posR => fr posR)

  public export
  Applicative BTreeLeaf' where
    pure a = LeafS <| \_ => a
    fs <*> vs = uncurry ($) <$> liftA2BBTreeLeaf' fs vs 


  ||| Just summing up elements of the tree given by the Rig a structure
  public export
  Rig a => Algebra BTreeLeaf' a where
    reduce (LeafS <| v) = v AtLeaf
    reduce ((NodeS l r) <| v) =
      let leftSubtree = l <| \posL => v (GoLLeaf posL)
          rightSubtree = r <| \posR => v (GoRLeaf posR)
      in reduce {f=BTreeLeaf'} leftSubtree ~+~
         reduce {f=BTreeLeaf'} rightSubtree


namespace BTreeNodeInstances
  -- TODO missing Eq instance for trees

  impossibleCase : FinBTreeNode LeafS -> (a, b)
  impossibleCase Root impossible
  impossibleCase (GoL x) impossible
  impossibleCase (GoR x) impossible

  ||| Combine two BTreeNode' structures, pairing values at corresponding nodes.
  ||| The resulting shape is the intersection of the input shapes.
  public export
  liftA2BTreeNode' : BTreeNode' a -> BTreeNode' b -> BTreeNode' (a, b)
  liftA2BTreeNode' ((NodeS l1 r1) <| f1) ((NodeS l2 r2) <| f2) =
    let (ls <| fl) = liftA2BTreeNode' (l1 <| f1 . GoL) (l2 <| f2 . GoL)
        (rs <| fr) = liftA2BTreeNode' (r1 <| f1 . GoR) (r2 <| f2 . GoR)

        resultFunc : FinBTreeNode (NodeS ls rs) -> (a, b)
        resultFunc Root = (f1 Root, f2 Root)
        resultFunc (GoL posL) = fl posL
        resultFunc (GoR posR) = fr posR
    in (NodeS ls rs <| resultFunc)
  liftA2BTreeNode' _ _ = LeafS <| impossibleCase

  public export
  Applicative BTreeNode' where
    pure a = NodeS LeafS LeafS <| \_ => a
    fs <*> vs = uncurry ($) <$> liftA2BTreeNode' fs vs 

  public export
  Rig a => Algebra BTreeNode' a where
    reduce (LeafS <| v) = zero
    reduce ((NodeS l r) <| v) = v Root ~+~
        reduce {f=BTreeNode'} (l <| v . GoL) ~+~
        reduce {f=BTreeNode'} (r <| v . GoR)
  
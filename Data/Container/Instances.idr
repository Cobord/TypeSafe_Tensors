module Data.Container.Instances

import Data.Fin
import Data.Vect


import Data.Container.Definition
import Tensor.Naperian
import Misc
import Data.Tree

%hide Data.Vect.fromList


||| Shapes of binary trees
public export
data BTreeShape : Type where
  LeafS : BTreeShape
  NodeS : BTreeShape -> BTreeShape -> BTreeShape

||| Positions corresponding to internal nodes within a BTreeShape shape.
public export
data FinTreeNode : (b : BTreeShape) -> Type where
  Root : {l, r : BTreeShape} -> FinTreeNode (NodeS l r)
  GoL  : {l, r : BTreeShape} -> FinTreeNode l -> FinTreeNode (NodeS l r)
  GoR  : {l, r : BTreeShape} -> FinTreeNode r -> FinTreeNode (NodeS l r)

||| Positions corresponding to leaves within a BTreeShape shape.
public export
data FinTreeLeaf : (b : BTreeShape) -> Type where
  AtLeaf : FinTreeLeaf LeafS
  GoLLeaf : {l, r : BTreeShape} -> FinTreeLeaf l -> FinTreeLeaf (NodeS l r)
  GoRLeaf : {l, r : BTreeShape} -> FinTreeLeaf r -> FinTreeLeaf (NodeS l r)

-- Examples
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

||| Trees with data stored at nodes
public export
TreeNodeCont : Cont
TreeNodeCont = (b : BTreeShape) !> FinTreeNode b

||| Trees with data stored at leaves
public export
TreeLeafCont : Cont
TreeLeafCont = (b : BTreeShape) !> FinTreeLeaf b


||| Isomorphic to Pair
public export
Pair' : Type -> Type
Pair' = Ext PairCont

public export
VectOld : (n : Nat) -> Type -> Type
VectOld n x = (VectCont n) `fof` x

||| Isomorphic to Vect
public export
record Vect' (n : Nat) (x : Type) where
  constructor MkVect'
  GetVect' : (VectCont n) `fof` x

||| Isomorphic to Maybe
public export
Maybe' : Type -> Type
Maybe' = Ext MaybeCont

||| Isomorphic to List
public export
List' : Type -> Type
List' = Ext ListCont

public export
fromList : List x -> List' x
fromList [] = (0 <| absurd)
fromList (x :: xs) = let (l <| c) = fromList xs
                     in (S l <| addBeginning x c)


public export
fromVectOld : Vect n x -> VectOld n x
fromVectOld v = () <| \i => index i v

public export
fromVect : Vect n x -> Vect' n x
fromVect v = MkVect' $ () <| \i => index i v

public export
toVect : {n : Nat} -> Vect' n x -> Vect n x
toVect (MkVect' (_ <| indexCont)) = vectTabulate indexCont


public export
Functor (Vect' n) where
  map f (MkVect' a) = MkVect' $ map {f=(Ext (VectCont n))} f a

public export
{n : Nat} -> Applicative (Vect' n) where
  pure a = fromVect (pure a)
  fs <*> vs = fromVect $ toVect fs <*> toVect vs 

public export
{n : Nat} -> Applicative (Ext (VectCont n)) where
  pure a = GetVect' $ fromVect $ pure a
  fs <*> vs = GetVect' $ fromVect $ toVect (MkVect' fs) <*> toVect (MkVect' vs)


||| Isomorphic to Trees with data at only nodes
public export
TreeNode' : Type -> Type
TreeNode' = Ext TreeNodeCont

||| Isomorphic to Trees with data only at leaves
public export
TreeLeaf' : Type -> Type
TreeLeaf' = Ext TreeLeafCont

namespace TreeNodeInstances

  impossibleCase : FinTreeNode LeafS -> (a, b)
  impossibleCase Root impossible
  impossibleCase (GoL x) impossible
  impossibleCase (GoR x) impossible

  ||| Extract the function for the left subtree
  getLeftFunc : {l, r : BTreeShape}
    -> (FinTreeNode (NodeS l r) -> x) -> (FinTreeNode l -> x)
  getLeftFunc {l} {r} f = \posL => f (GoL {l=l} {r=r} posL)

  ||| Extract the function for the right subtree
  getRightFunc : {l, r : BTreeShape}
    -> (FinTreeNode (NodeS l r) -> x) -> (FinTreeNode r -> x)
  getRightFunc {l} {r} f = \posR => f (GoR {l=l} {r=r} posR)

  ||| Combine two TreeNode' structures, pairing values at corresponding nodes.
  ||| The resulting shape is the intersection of the input shapes.
  public export
  liftA2TreeNode' : TreeNode' a -> TreeNode' b -> TreeNode' (a, b)
  liftA2TreeNode' ((NodeS l1 r1) <| f1) ((NodeS l2 r2) <| f2) =
    let (ls <| fl) : TreeNode' (a, b) = liftA2TreeNode' (l1 <| getLeftFunc f1) (l2 <| getLeftFunc f2)

        (rs <| fr) : TreeNode' (a, b) = liftA2TreeNode' (r1 <| getRightFunc f1) (r2 <| getRightFunc f2)

        resultFunc : FinTreeNode (NodeS ls rs) -> (a, b)
        resultFunc Root = (f1 Root, f2 Root)
        resultFunc (GoL posL) = fl posL
        resultFunc (GoR posR) = fr posR
    in (NodeS ls rs <| resultFunc)
  liftA2TreeNode' _ _ = LeafS <| impossibleCase

  public export
  Applicative TreeNode' where
    pure a = NodeS LeafS LeafS <| \_ => a
    fs <*> vs = uncurry ($) <$> liftA2TreeNode' fs vs 


namespace TreeLeafInstances
    public export
    liftA2BTreeLeaf' : TreeLeaf' a -> TreeLeaf' b -> TreeLeaf' (a, b)
    liftA2BTreeLeaf' (LeafS <| v) (LeafS <| v') = LeafS <| (\x => (v x, v' x))
    liftA2BTreeLeaf' (LeafS <| v) (NodeS l' r' <| v') = NodeS l' r' <| ?aaa
    liftA2BTreeLeaf' (NodeS l r <| v) (LeafS <| v') = ?liftA2BTreeLeaf'_rhs_4
    liftA2BTreeLeaf' (NodeS l r <| v) (NodeS l' r' <| v') = ?liftA2BTreeLeaf'_rhs_6 <| ?vlvlvl

    public export
    Applicative TreeLeaf' where
      pure a = LeafS <| \_ => a
      fs <*> vs = uncurry ($) <$> liftA2BTreeLeaf' fs vs 

fromTreeHelper : FinTreeNode LeafS -> a
fromTreeHelper Root impossible
fromTreeHelper (GoL x) impossible
fromTreeHelper (GoR x) impossible

public export
fromTreeNode : BTreeNode a -> TreeNode' a
fromTreeNode (Leaf ()) = (LeafS <| fromTreeHelper)
fromTreeNode (Node node leftTree rightTree)
  = let (lts <| ltc) = fromTreeNode leftTree
        (rts <| rtc) = fromTreeNode rightTree
    in (NodeS lts rts <| \pos =>
          case pos of
            Root => node
            GoL posL => ltc posL
            GoR posR => rtc posR)

public export
fromTreeLeaf : BTreeLeaf a -> TreeLeaf' a
fromTreeLeaf (Leaf leaf) = LeafS <| \_ => leaf
fromTreeLeaf (Node node lt rt) =
  let (shL <| fnL) = fromTreeLeaf lt
      (shR <| fnR) = fromTreeLeaf rt
  in (NodeS shL shR <| \pos =>
        case pos of
          GoLLeaf posL => fnL posL
          GoRLeaf posR => fnR posR)
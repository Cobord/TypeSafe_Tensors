module Data.Container.Definition

import Data.Fin
import Data.Vect

import Data.Tree

%hide Data.Vect.fromList
%hide Builtin.fst

||| Shapes of binary trees
public export
data BTreeShape : Type where
  LeafS : BTreeShape
  NodeS : BTreeShape -> BTreeShape -> BTreeShape

||| Positions corresponding to internal nodes within a BTreeShape shape.
||| This type is uninhabited for the LeafS shape, as leaves have no internal nodes.
public export
data FinTreeNode : (b : BTreeShape) -> Type where
  -- Represents the position *at* the root of the current NodeS structure.
  Root : {l, r : BTreeShape} -> FinTreeNode (NodeS l r)

  -- Represents a position located within the *left* subtree 'l'.
  -- It takes a position 'FinTreeNode l' and "lifts" it into the parent context '(NodeS l r)'.
  GoL  : {l, r : BTreeShape} -> FinTreeNode l -> FinTreeNode (NodeS l r)

  -- Represents a position located within the *right* subtree 'r'.
  -- It takes a position 'FinTreeNode r' and "lifts" it into the parent context '(NodeS l r)'.
  GoR  : {l, r : BTreeShape} -> FinTreeNode r -> FinTreeNode (NodeS l r)

||| Positions corresponding to leaves within a BTreeShape shape.
public export
data FinTreeLeaf : (b : BTreeShape) -> Type where
  AtLeaf : FinTreeLeaf LeafS
  GoLLeaf : {l, r : BTreeShape} -> FinTreeLeaf l -> FinTreeLeaf (NodeS l r)
  GoRLeaf : {l, r : BTreeShape} -> FinTreeLeaf r -> FinTreeLeaf (NodeS l r)

-- Taken from Andre's code

||| A container is a product of a shape and a set of positions indexed by that shape
||| They can be used to describe data types
public export
record Cont where
  constructor (!>)
  ||| Shapes
  shp : Type
  ||| Positions
  pos : shp -> Type

export typebind infixr 0 !>

%name Cont c, c', c''

-- Examples
public export
PairCont : Cont
PairCont = (_ : Unit) !> Bool

public export
VectCont : (n : Nat) -> Cont
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

||| Extension of a container
||| This allows us to talk about the content, or payload of a container
public export
ext : Cont -> Type -> Type
ext (shp !> pos) x = (s : shp ** pos s -> x)

public export
extMap : (c : Cont) -> (a -> b) -> ext c a -> ext c b
extMap (shp !> pos) f ((s ** v)) = (s ** f . v)


||| Isomorphic to Pair
public export
Pair' : Type -> Type
Pair' = ext PairCont

||| Isomorphic to Vect
public export
Vect' : (n : Nat) -> Type -> Type
Vect' n = ext (VectCont n)

||| Isomorphic to Maybe
public export
Maybe' : Type -> Type
Maybe' = ext MaybeCont

||| Isomorphic to List
public export
List' : Type -> Type
List' = ext ListCont

public export
fromList : List x -> List' x
fromList [] = (0 ** absurd)
fromList (x :: xs) = let (l ** c) = fromList xs
                     in (S l ** \k => case k of
                                         FZ => x
                                         FS k' => c k')

||| Isomorphic to Trees with data at only nodes
public export
TreeNode' : Type -> Type
TreeNode' = ext TreeNodeCont

fromTreeHelper : FinTreeNode LeafS -> a
fromTreeHelper Root impossible
fromTreeHelper (GoL x) impossible
fromTreeHelper (GoR x) impossible

public export
fromTree : BTreeNode a -> TreeNode' a
fromTree (Leaf ()) = (LeafS ** fromTreeHelper)
fromTree (Node node leftTree rightTree)
  = let (lts ** ltc) = fromTree leftTree
        (rts ** rtc) = fromTree rightTree
    in (NodeS lts rts ** \pos =>
          case pos of
            Root => node
            GoL posL => ltc posL
            GoR posR => rtc posR)


||| Isomorphic to Trees with data only at leaves
TreeLeaf' : Type -> Type
TreeLeaf' = ext TreeLeafCont


hhh : FinTreeLeaf (NodeS LeafS LeafS) -> Int
hhh (GoLLeaf AtLeaf) = 3
hhh (GoRLeaf AtLeaf) = 4

t : TreeLeaf' Int
t = (NodeS LeafS LeafS ** hhh)

vv : Vect' 9 Int
vv = (() ** ?vv_rhs)

ll : List' Int
ll = fromList [1,2,3,4]


public export
infixr 0 ><
||| Hancock, or Dirichlet tensor product
(><) : Cont -> Cont -> Cont
(><) (shp !> pos) (shp' !> pos') = ((s, s') : (shp, shp')) !> (pos s, pos' s')
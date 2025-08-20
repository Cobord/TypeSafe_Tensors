module Data.Container.Instances

import Data.Fin
import Data.Vect
import Data.List
import Data.DPair

import Data.Container.Definition
import Data.Container.Applicative.Definition
import Data.Functor.Naperian
import Data.List.Quantifiers
import Misc
import Data.Algebra
import Data.Tree
import public Data.Container.TreeUtils -- rexport all the stuff inside

%hide Data.Vect.fromList


||| Examples that do not require any additional constraints such as Applicative
namespace MainExamples
  ||| Empty container, isomorphic to Void
  public export
  Empty : Cont
  Empty = (x : Void) !> absurd x

  ||| Container with a single shape, but no positions, isomorphic to Unit : Type
  public export
  Unit : Cont
  Unit = (_ : Unit) !> Void 

  ||| Container of a single thing
  public export
  Scalar : Cont
  Scalar = (_ : Unit) !> Unit

  ||| Product, container of two things
  public export
  Pair : Cont
  Pair = (_ : Unit) !> Bool

  ||| Coproduct, container of either one of two things
  public export
  Either : Cont
  Either = (_ : Bool) !> Unit

  ||| +1, container of either one thing, or nothing
  public export
  Maybe : Cont
  Maybe = (b : Bool) !> (if b then Unit else Void)

  ||| List, container with an arbitrary number of things
  public export
  List : Cont
  List = (n : Nat) !> Fin n
  
  ||| Vect, container of a fixed/known number of things
  public export
  Vect : Nat -> Cont
  Vect n = (_ : Unit) !> Fin n

  ||| Container of an infinite number of things
  public export
  Stream : Cont
  Stream = (_ : Unit) !> Nat

  ||| Container of things stored at nodes and leaves of a binary tree
  public export
  BinTree : Cont
  BinTree = (b : BinTreeShape) !> BinTreePos b
  
  ||| Container of things stored at nodes of a binary tree
  public export
  BinTreeNode : Cont
  BinTreeNode = (b : BinTreeShape) !> BinTreePosNode b
  
  ||| Container of things stored at leaves of a binary tree
  public export
  BinTreeLeaf : Cont
  BinTreeLeaf = (b : BinTreeShape) !> BinTreePosLeaf b
  
  ||| Generalisation of Rose trees with a container
  ||| of subtrees (container whose extension is applicative)
  ||| instead of a list of a subtrees
  public export
  ApplicativeRoseTree : ContA -> Cont
  ApplicativeRoseTree c = (t : RoseTreeShape c) !> RoseTreePos c t

  ||| Tensors are containers
  ||| TODO not used yet, new finding
  public export
  Tensor : List Cont -> Cont
  Tensor cs = composeContainers cs
  
  ||| Every lens gives rise to a container
  ||| The set of shapes is the lens itself
  ||| The set of positions is the inputs to the lens
  ||| This is the closure with respect to the Hancock tensor product
  public export
  InternalLens : Cont -> Cont -> Cont
  InternalLens c d
    = (f : ((x : c.shp) -> (y : d.shp ** d.pos y -> c.pos x)))
      !> (xx : c.shp ** d.pos (fst (f xx)))


  ||| From https://www.cs.ox.ac.uk/people/samuel.staton/papers/cie10.pdf
  public export
  CartesianClosure : Cont -> Cont -> Cont
  CartesianClosure c d
    = (f : ((x : c.shp) -> (y : d.shp ** d.pos y -> Maybe (c.pos x))))
      !> (xx : c.shp ** yy' : d.pos (fst (f xx)) ** ?hh)

namespace ExtensionsOfMainExamples
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
  Vect' n = Ext (Vect n)

  ||| Isomorphic to Stream
  public export
  Stream' : Type -> Type
  Stream' = Ext Stream

  ||| Isomorphic to Data.Tree.BinTreeSame
  public export
  BinTree' : Type -> Type
  BinTree' = Ext BinTree

  ||| Isomorphic to Data.Tree.BinTreeNode
  public export
  BinTreeNode' : Type -> Type
  BinTreeNode' = Ext BinTreeNode
  
  ||| Isomorphic to Data.Tree.BinTreeLeaf
  public export
  BinTreeLeaf' : Type -> Type
  BinTreeLeaf' = Ext BinTreeLeaf

  ||| Isomorphic to Data.Tree.ApplicativeRoseTree (TODO)
  public export
  ApplicativeRoseTree' : (c : ContA) -> Type -> Type
  ApplicativeRoseTree' c = Ext (ApplicativeRoseTree c)

  ||| Isomorphic to Data.Tensor.TensorA
  ||| todo
  public export
  Tensor' : List Cont -> Type -> Type
  Tensor' cs = Ext (Tensor cs)


namespace ConversionFunctions
  public export
  fromIdentity : a -> Scalar' a
  fromIdentity a = () <| (\_ => a)

  public export
  toIdentity : Scalar' a -> a
  toIdentity (() <| f) = f ()

  public export
  fromMaybe : Maybe a -> Maybe' a
  fromMaybe Nothing = (False <| absurd)
  fromMaybe (Just a) = (True <| \_ => a)

  public export
  toMaybe : Maybe' a -> Maybe a
  toMaybe (False <| absurd) = Nothing
  toMaybe (True <| f) = Just (f ())

  public export
  fromList : List a -> List' a
  fromList [] = (0 <| absurd)
  fromList (x :: xs) = let (l <| c) : List' a := fromList xs
                       in (S l <| addBeginning x c)

  public export
  toList : List' a -> List a
  toList (0 <| _) = []
  toList ((S k) <| ind) = let (x, c) = removeBeginning ind
                          in x :: toList (k <| c)
  
  public export
  fromVect : Vect n a -> Vect' n a
  fromVect v = () <| \i => index i v
  
  public export
  toVect : {n : Nat} -> Vect' n a -> Vect n a
  toVect (_ <| indexCont) = vectTabulate indexCont

  public export
  fromBinTreeSame : BinTreeSame a -> BinTree' a
  fromBinTreeSame (Leaf x) = LeafS <| \_ => x
  fromBinTreeSame (Node x lt rt) =
    let (lts <| ltc) = fromBinTreeSame lt
        (rts <| rtc) = fromBinTreeSame rt
    in NodeS lts rts <| \case
        DoneNode => x
        GoLeft posL => ltc posL
        GoRight posR => rtc posR

  public export
  toBinTreeSame : BinTree' a -> BinTreeSame a
  toBinTreeSame (LeafS <| indexCont) = Leaf (indexCont DoneLeaf)
  toBinTreeSame (NodeS lt rt <| indexCont) =
    Node (indexCont DoneNode)
         (toBinTreeSame (lt <| indexCont . GoLeft))
         (toBinTreeSame (rt <| indexCont . GoRight))
  
  
  public export
  fromTreeHelper : BinTreePosNode LeafS -> a
  fromTreeHelper Done impossible
  fromTreeHelper (GoLeft x) impossible
  fromTreeHelper (GoRight x) impossible
  
  public export
  fromBinTreeNode : BinTreeNode a -> BinTreeNode' a
  fromBinTreeNode (Leaf ()) = LeafS <| fromTreeHelper
  fromBinTreeNode (Node node leftTree rightTree)
    = let (lts <| ltc) = fromBinTreeNode leftTree
          (rts <| rtc) = fromBinTreeNode rightTree
      in (NodeS lts rts <| \case
            Done => node
            GoLeft posL => ltc posL
            GoRight posR => rtc posR)

  public export
  toBinTreeNode : BinTreeNode' a -> BinTreeNode a
  toBinTreeNode (LeafS <| indexCont) = Leaf ()
  toBinTreeNode (NodeS lt rt <| indexCont) = 
    Node (indexCont Done)
         (toBinTreeNode (lt <| indexCont . GoLeft))
         (toBinTreeNode (rt <| indexCont . GoRight))
  
  public export
  fromBinTreeLeaf : BinTreeLeaf a -> BinTreeLeaf' a
  fromBinTreeLeaf (Leaf leaf) = LeafS <| \_ => leaf
  fromBinTreeLeaf (Node node lt rt) =
    let (shL <| fnL) = fromBinTreeLeaf lt
        (shR <| fnR) = fromBinTreeLeaf rt
    in NodeS shL shR <| \case
          GoLeft posL => fnL posL
          GoRight posR => fnR posR

  public export
  toBinTreeLeaf : BinTreeLeaf' a -> BinTreeLeaf a
  toBinTreeLeaf (LeafS <| content) = Leaf (content Done)
  toBinTreeLeaf (NodeS l r <| content) =
    Node' (toBinTreeLeaf (l <| content . GoLeft))
          (toBinTreeLeaf (r <| content . GoRight))

  ||| Indexing an element of `xs` and then applying `f` to it is the same as
  ||| mapping `f` over xs, and then indexing the result
  public export
  mapIndexPreserve : {0 f : a -> b} ->
    (xs : List a) ->
    (i : Fin (length (f <$> xs))) ->
    f (index' xs (rewrite sym (lengthMap {f=f} xs) in i))
      = index' (f <$> xs) i
  mapIndexPreserve (x :: xs) FZ = Refl
  mapIndexPreserve (x :: xs) (FS j) = mapIndexPreserve xs j

public export
FromConcrete Scalar where
  concreteType = id
  concreteFunctor = MkFunctor id
  fromConcreteTy = fromIdentity
  toConcreteTy = toIdentity

public export
FromConcrete Maybe where
  concreteType = Maybe
  concreteFunctor = %search
  fromConcreteTy = fromMaybe
  toConcreteTy = toMaybe

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
FromConcrete BinTree where
  concreteType = BinTreeSame
  concreteFunctor = %search
  fromConcreteTy = fromBinTreeSame
  toConcreteTy = toBinTreeSame

public export
FromConcrete BinTreeNode where
  concreteType = BinTreeNode
  concreteFunctor = %search
  fromConcreteTy = fromBinTreeNode
  toConcreteTy = toBinTreeNode

public export
FromConcrete BinTreeLeaf where
  concreteType = BinTreeLeaf
  concreteFunctor = %search
  fromConcreteTy = fromBinTreeLeaf
  toConcreteTy = toBinTreeLeaf

public export
concreteTypeTensor : (shape : List Cont) ->
  (allConcrete : AllConcrete shape) =>
  Type -> Type
concreteTypeTensor [] {allConcrete = []} = concreteType {cont=Scalar}
concreteTypeTensor [c] {allConcrete = Cons} = concreteType {cont=c}
concreteTypeTensor (c :: d :: cs) {allConcrete = Cons @{fc}}
  = (concreteType @{fc}) . (concreteTypeTensor (d :: cs))


public export
concreteTypeFunctor : {shape : List Cont} ->
  (allConcrete : AllConcrete shape) =>
  Functor (concreteTypeTensor shape)
concreteTypeFunctor {shape = []} {allConcrete = []}
  = concreteFunctor {cont=Scalar}
concreteTypeFunctor {shape = [_]} {allConcrete = Cons @{fc}}
  = concreteFunctor @{fc}
concreteTypeFunctor {shape = (c :: d :: cs)} {allConcrete = Cons @{fc}}
  = Functor.Compose @{concreteFunctor @{fc} } @{concreteTypeFunctor}

public export
concreteToExtensions : {shape : List Cont} ->
  (allConcrete : AllConcrete shape) =>
  concreteTypeTensor shape a -> composeExtensions shape a
concreteToExtensions {shape = []} {allConcrete = []} ct = fromConcreteTy ct
concreteToExtensions {shape = [_]} {allConcrete = Cons} ct = fromConcreteTy ct
concreteToExtensions {shape = (_ :: _ :: _)} {allConcrete = Cons} ct = 
  concreteToExtensions <$> fromConcreteTy ct 

public export
extensionsToConcreteType : {shape : List Cont} ->
  (allConcrete : AllConcrete shape) =>
  composeExtensions shape a -> concreteTypeTensor shape a
extensionsToConcreteType {shape = []} {allConcrete = []} ct = toConcreteTy ct
extensionsToConcreteType {shape = [c]} {allConcrete = Cons} ct = toConcreteTy ct
extensionsToConcreteType {shape = (_ :: _ :: _)} {allConcrete = Cons @{fc}} ct 
  = (map @{concreteFunctor @{fc}} extensionsToConcreteType) (toConcreteTy ct)

public export
fromTensor : {shape : List Cont} ->
  (allConcrete : AllConcrete shape) =>
  concreteTypeTensor shape a -> Tensor' shape a
fromTensor = toContainerComp . concreteToExtensions

  
public export
toTensor : {shape : List Cont} ->
  (allConcrete : AllConcrete shape) =>
  Tensor' shape a -> concreteTypeTensor shape a
toTensor = extensionsToConcreteType . fromContainerComp


public export
{shape : List Cont} ->
(allConcrete : AllConcrete shape) =>
FromConcrete (Tensor shape) where
  concreteType = concreteTypeTensor shape {allConcrete}
  concreteFunctor = concreteTypeFunctor {shape} {allConcrete}
  fromConcreteTy = fromTensor
  toConcreteTy = toTensor


baal : FromConcrete Scalar
baal = %search

baa : FromConcrete Maybe
baa = %search

aa : AllConcrete [List, List]
aa = %search

ca : FromConcrete (Tensor [List, List])
-- ca = %search

-- caa : FromConcrete (Tensor [List, Maybe])
-- caa = %search

--tt : Tensor' [List, Maybe] Int
--- tt = fromConcreteTy ?aaaa


-- TODO should all of these instances be defined in terms of their concrete ones?
-- i.e. simply via translation functions to concreteTypes we defined above?
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
  ||| Effectively it behaves like a cartesian product
  public export 
  [cartProdInstance] Applicative List' where
    pure = fromList . pure
    fs <*> vs = fromList $ toList fs <*> toList vs

  public export
  listZip' : List' a -> List' b -> List' (a, b)
  listZip' l1 l2 = fromList $ listZip (toList l1) (toList l2)

  ||| This another List applicative, behaving like the usual zip one
  ||| It appears that List doesn't have the concret Zippable instance written
  ||| Only one in Data.Zippable that follows from Applicative, which isn't the one we want
  public export
  Applicative List' where
    pure = fromList . pure
    fs <*> vs = fromList $ uncurry ($) <$> listZip (toList fs) (toList vs)


namespace BinTreeInstances
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


namespace BinTreeLeafInstances
  public export
  showBinTreeLeaf' : Show a => BinTreeLeaf' a -> String
  showBinTreeLeaf' (LeafS <| content) = "Leaf (" ++ show (content Done) ++ ")"
  showBinTreeLeaf' ((NodeS l r) <| content) =
    let leftSubtree : BinTreeLeaf' a = (l <| \posL => content (GoLeft posL))
        rightSubtree : BinTreeLeaf' a = (r <| \posR => content (GoRight posR))
    in "Node (" ++ showBinTreeLeaf' leftSubtree ++ ") (" ++ showBinTreeLeaf' rightSubtree ++ ")"

  partial -- not partial but not sure how to convince Idris totality checker
  public export
  Show a => Show (BinTreeLeaf' a) where
    show t = show (toBinTreeLeaf t)

  public export
  Eq a => Eq (BinTreeLeaf' a) where
    (LeafS <| v) == (LeafS <| v') = v Done == v' Done
    (NodeS l r <| v) == (NodeS l' r' <| v') =
      (l == l') && (r == r') && ?vnm -- Assuming Eq BinTreeShape is defined elsewhere
    _ == _ = False

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


  ||| Just summing up elements of the tree given by the Num a structure
  public export
  Num a => Algebra BinTreeLeaf' a where
    reduce (LeafS <| v) = v Done
    reduce (NodeS l r <| v) =
      let leftSubtree = l <| v . GoLeft
          rightSubtree = r <| v . GoRight
      in reduce {f=BinTreeLeaf'} leftSubtree +
         reduce {f=BinTreeLeaf'} rightSubtree


namespace BinTreeNodeInstances
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

  public export
  Num a => Algebra BinTreeNode' a where
    reduce (LeafS <| v) = fromInteger 0
    reduce (NodeS l r <| v) = v Done +
      reduce {f=BinTreeNode'} (l <| v . GoLeft) +
      reduce {f=BinTreeNode'} (r <| v . GoRight)



data AllAlgebra : (shape : List Cont) -> (dtype : Type) -> Type where
  Nil : AllAlgebra [] a
  Cons : (alg : Algebra (Ext c) (Tensor' cs a)) =>
    (allAlg : AllAlgebra cs a) =>
    AllAlgebra (c :: cs) a


public export
reduceTensor : {shape : List Cont} ->
  (allAlgebra : AllAlgebra shape a) =>
  Tensor' shape a -> a
reduceTensor {shape = []} {allAlgebra = []} t = toIdentity t
reduceTensor {shape = [c]} {allAlgebra = Cons {alg}} t = ?reduceTensor_rhs_1
reduceTensor {shape = (c :: cs)} {allAlgebra = Cons {alg} {allAlg}} t
  = let tt = fromContainerComp t
    in ?reduceTensor_rhs_2

public export
{shape : List Cont} ->
(allAlgebra : AllAlgebra shape a) =>
Algebra (Tensor' shape) a where
  reduce = reduceTensor


  --reduceTensorA {allAlg = []} (TZ val) = val
  --reduceTensorA {allAlg = ((::) {allAlg=cs})} (TS xs)
  --  = reduceTensorA $ reduce xs
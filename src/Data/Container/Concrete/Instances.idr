module Data.Container.Concrete.Instances

import Data.Fin
import Data.Vect
import Data.List
import Data.DPair

import Data.Container.Object.Definition
import Data.Container.Object.Instances
import Data.Container.Concrete.Definition
import Data.Container.Extension.Definition
import Data.Container.Extension.Instances

import Data.Container.Products


import Data.Functor.Naperian
import Data.Tree

import Misc


public export
{c, d : Cont} -> FromConcrete c => FromConcrete d => FromConcrete (c >@ d) where
  concreteType = ?oone
  concreteFunctor = ?twoo
  fromConcreteTy = ?threee
  toConcreteTy = ?fourr



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

  -- ||| Indexing an element of `xs` and then applying `f` to it is the same as
  -- ||| mapping `f` over xs, and then indexing the result
  -- public export
  -- mapIndexPreserve : {0 f : a -> b} ->
  --   (xs : List a) ->
  --   (i : Fin (length (f <$> xs))) ->
  --   f (index' xs (rewrite sym (lengthMap {f=f} xs) in i))
  --     = index' (f <$> xs) i
  -- mapIndexPreserve (x :: xs) FZ = Refl
  -- mapIndexPreserve (x :: xs) (FS j) = mapIndexPreserve xs j


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

-- public export
-- concreteTypeTensor : (shape : List Cont) ->
--   (allConcrete : AllConcrete shape) =>
--   Type -> Type
-- concreteTypeTensor [] {allConcrete = []} = concreteType {cont=Scalar}
-- concreteTypeTensor (c :: cs) {allConcrete = Cons @{fc}}
--   = (concreteType @{fc}) . (concreteTypeTensor cs)

gq : Vect' 9 Char
gq = fromConcreteTy ?tuuuumnu

public export
concreteTypeComposition : (shape : List Cont) ->
  (allConcrete : AllConcrete shape) =>
  Type -> Type
concreteTypeComposition [] = concreteType {cont=Scalar}
concreteTypeComposition (c :: cs) {allConcrete = Cons}
  = concreteType {cont=c} . concreteTypeComposition cs

%hint
public export
ffInterf : {shape : List Cont} ->
(allConcrete : AllConcrete shape) =>
FromConcrete (Tensor shape)
ffInterf = ?todooo
  -- concreteType = concreteTypeComposition shape
  -- concreteFunctor = ?two
  -- fromConcreteTy = ?three
  -- toConcreteTy = ?four


baal : FromConcrete Scalar
baal = %search

baa : FromConcrete Maybe
baa = %search

vv : FromConcrete (Vect 3)
vv = %search

aa : AllConcrete [Vect 3, List]
aa = %search

-- aab : FromConcrete (composeContainers [Vect 3, List])
-- aab = %search

%hint
aabt : FromConcrete (List >@ List)
aabt = ?tuuu


aabt2 : FromConcrete (List >@ List)
aabt2 = %search
  
-- 
-- ca : FromConcrete (Tensor [List, List])
-- ca = %search


{-
public export
concreteTypeFunctor : {shape : List Cont} ->
  (allConcrete : AllConcrete shape) =>
  Functor (concreteTypeTensor shape)
concreteTypeFunctor {shape = []} {allConcrete = []}
  = concreteFunctor {cont=Scalar}
concreteTypeFunctor {shape = (c :: cs)} {allConcrete = Cons @{fc}}
  = Functor.Compose @{concreteFunctor @{fc} } @{concreteTypeFunctor}

public export
concreteToExtensions : {shape : List Cont} ->
  (allConcrete : AllConcrete shape) =>
  concreteTypeTensor shape a -> composeExtensions shape a
concreteToExtensions {shape = []} {allConcrete = []} ct = fromConcreteTy ct
concreteToExtensions {shape = (_ :: _)} {allConcrete = Cons} ct = 
  concreteToExtensions <$> fromConcreteTy ct 

public export
extensionsToConcreteType : {shape : List Cont} ->
  (allConcrete : AllConcrete shape) =>
  composeExtensions shape a -> concreteTypeTensor shape a
extensionsToConcreteType {shape = []} {allConcrete = []} ct = toConcreteTy ct
extensionsToConcreteType {shape = (_ :: _)} {allConcrete = Cons @{fc}} ct 
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
 -}


-- caa : FromConcrete (Tensor [List, Maybe])
-- caa = %search

--tt : Tensor' [List, Maybe] Int
--- tt = fromConcreteTy ?aaaa

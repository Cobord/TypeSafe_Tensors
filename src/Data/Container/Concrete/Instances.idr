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

import public Data.Functor.Naperian
import public Data.Tree

import Misc

namespace ConversionFunctions
  public export
  toScalar : a -> Scalar' a
  toScalar a = () <| (\_ => a)

  public export
  extract : Scalar' a -> a
  extract (() <| f) = f ()

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
  toVect (_ <| index) = Vect.Fin.tabulate index

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
  toBinTreeSame (LeafS <| index) = Leaf (index DoneLeaf)
  toBinTreeSame (NodeS lt rt <| index) =
    Node (index DoneNode)
         (toBinTreeSame (lt <| index . GoLeft))
         (toBinTreeSame (rt <| index . GoRight))
  
  
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
  toBinTreeNode (LeafS <| index) = Leaf ()
  toBinTreeNode (NodeS lt rt <| index) = 
    Node (index Done)
         (toBinTreeNode (lt <| index . GoLeft))
         (toBinTreeNode (rt <| index . GoRight))
  
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
  fromConcreteTy = pure
  toConcreteTy = extract

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


namespace TensorFromConcrete
  public export
  concreteTypeTensor : (shape : List Cont) ->
    (allConcrete : AllConcrete shape) =>
    Type -> Type
  concreteTypeTensor [] {allConcrete = []} = concreteType {cont=Scalar}
  concreteTypeTensor (c :: cs) {allConcrete = Cons @{fc}}
    = (concreteType @{fc}) . (concreteTypeTensor cs)
  
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
  toTensor : {shape : List Cont} ->
    (allConcrete : AllConcrete shape) =>
    concreteTypeTensor shape a -> Tensor' shape a
  toTensor = fromExtensionComposition . concreteToExtensions
  
  public export
  fromTensor : {shape : List Cont} ->
    (allConcrete : AllConcrete shape) =>
    Tensor' shape a -> concreteTypeTensor shape a
  fromTensor = extensionsToConcreteType . toExtensionComposition

-- Not sure how to do it other than for a fixed number of axes
-- all general solutions break when trying to be used with Idris interfaces
public export
{c : Cont} -> AllConcrete [c] =>
  FromConcrete (Tensor [c]) where
  concreteType = concreteTypeTensor [c]
  concreteFunctor = concreteTypeFunctor {shape = [c]}
  fromConcreteTy = toTensor
  toConcreteTy = fromTensor

public export
{c, d : Cont} -> AllConcrete [c, d] =>
  FromConcrete (Tensor ([c, d])) where
  concreteType = concreteTypeTensor [c, d]
  concreteFunctor = concreteTypeFunctor {shape = [c, d]}
  fromConcreteTy = toTensor
  toConcreteTy = fromTensor

public export
{c, d, e : Cont} -> AllConcrete [c, d, e] =>
  FromConcrete (Tensor ([c, d, e])) where
  concreteType = concreteTypeTensor [c, d, e]
  concreteFunctor = concreteTypeFunctor {shape = [c, d, e]}
  fromConcreteTy = toTensor
  toConcreteTy = fromTensor

public export
{c, d, e, f : Cont} -> AllConcrete [c, d, e, f] =>
  FromConcrete (Tensor ([c, d, e, f])) where
  concreteType = concreteTypeTensor [c, d, e, f]
  concreteFunctor = concreteTypeFunctor {shape = [c, d, e, f]}
  fromConcreteTy = toTensor
  toConcreteTy = fromTensor

public export
{c, d, e, f, g : Cont} -> AllConcrete [c, d, e, f, g] =>
  FromConcrete (Tensor ([c, d, e, f, g])) where
  concreteType = concreteTypeTensor [c, d, e, f, g]
  concreteFunctor = concreteTypeFunctor {shape = [c, d, e, f, g]}
  fromConcreteTy = toTensor
  toConcreteTy = fromTensor

at0 : FromConcrete (Tensor [])
at0 = %search

at1 : FromConcrete (Tensor [List])
at1 = %search

at10 : FromConcrete (Vect 4)
at10 = %search

atFinal : FromConcrete (Tensor [Vect 4, List])
atFinal = %search

atFinal2 : Tensor' [List, Maybe, Vect 2] Char
atFinal2 = fromConcreteTy ?huuu

oneMore : Tensor' [List] Int
oneMore = fromConcreteTy [1,2,3,4,5]

{-
public export
{shape : List Cont} -> FromConcrete (Tensor shape) where
  concreteType = ?onee
  concreteFunctor = ?two
  fromConcreteTy = ?three
  toConcreteTy = ?four


public export
{c, d : Cont} -> FromConcrete c => FromConcrete d => FromConcrete (c >@ d) where
  concreteType = ?oone
  concreteFunctor = ?twoooo
  fromConcreteTy = ?threeeee
  toConcreteTy = ?fourrerrr

-- public export
-- {c : Cont} -> FromConcrete c => FromConcrete (c >@ Scalar) where
--   concreteType = ?oneees
--   concreteFunctor = ?twooos
--   fromConcreteTy = ?threeees
--   toConcreteTy = ?fourrees

public export
{shape : List Cont} -> {c : Cont} -> FromConcrete c => FromConcrete (Tensor shape) => FromConcrete (c >@ Tensor shape) where
  concreteType = ?oones
  concreteFunctor = ?twoooos
  fromConcreteTy = ?threeeees
  toConcreteTy = ?fourrerrrs

aa : AllConcrete [Vect 3, List]
aa = ?vii -- %search


%hint
public export
makeConcreteFromList : {shape : List Cont} ->
  FromConcrete (Tensor shape)
makeConcreteFromList = ?todooo

%hint
makeConcreteNil : {c : Cont} -> FromConcrete c =>
  FromConcrete (c >@ Scalar)

%hint
makeConcreteCons : (v : FromConcrete c) =>   
  (ts : FromConcrete (Tensor cs)) =>
  FromConcrete (Tensor (c :: cs))
  -- concreteType = concreteTypeComposition shape
  -- concreteFunctor = ?two
  -- fromConcreteTy = ?three
  -- toConcreteTy = ?four

{-
Because of problems with Idris' interface and inference, need to 
write our own `fromConcreteTy` and `toConcreteTy` functions for tensor
 -}




-- at0 : FromConcrete (Tensor [])
-- at0 = %search
-- 
-- at10 : FromConcrete (Vect 4)
-- at10 = %search
-- 
-- at1 : FromConcrete (Tensor [List])
-- at1 = %search
-- 
-- atFinal : FromConcrete (Tensor [Vect 4, List])
-- atFinal = %search

-- record XRec (shape : List Cont) (a : Type) where
--   constructor MkXRec
--   stuff : Tensor' shape a
-- 
-- 
-- XTy : (shape : List Cont) -> Type -> Type
-- XTy shape = Tensor' shape
-- 
-- interface ITest (a : Type) where
-- 
-- {shape : List Cont} -> ITest (XTy shape a) where


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
-}



-- public export
-- index : (t : Tensor' shape a) -> (Tensor shape).pos (shapeExt (GetT t)) -> a
-- index t = Ext.index (GetT t)
module Data.Container.Extension.Instances

import Data.DPair

import Data.Container.Object.Definition
import Data.Container.Object.Instances
import Data.Container.Extension.Definition

import Data.Container.Products

import Data.Functor.Naperian

%hide Prelude.(<|)


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

  -- public export
  -- Tensor' : List Cont -> Type -> Type
  -- Tensor' cs = Ext (Tensor cs)

  public export
  record Tensor' (shape : List Cont) (a : Type) where
    constructor MkT
    GetT : Ext (Tensor shape) a


public export
composeExtensions : List Cont -> Type -> Type
composeExtensions [] a = Ext Scalar a
composeExtensions (c :: cs) a = Ext c (composeExtensions cs a)

public export
[fe] {shape : List Cont} -> Functor (composeExtensions shape) where
  map {shape = []} f = map f
  map {shape = (s :: ss)} f = (map @{fe} f <$>)

public export
EmptyExt : Ext (Nap l) Builtin.Unit
EmptyExt = () <| \_ => ()

public export
liftA2ConstCont : Ext (Nap l) a -> Ext (Nap l) b -> Ext (Nap l) (a, b)
liftA2ConstCont (() <| va) (() <| vb) = () <| (\x => (va x, vb x))

||| The extension of any container with a unit shape
||| is an applicative functor
||| Examples: Scalar, Pair, Vect n, Stream
||| Notably, List and Maybe are also applicative
public export
Applicative (Ext (Nap l)) where
  pure a = () <| (\_ => a)
  fs <*> xs = uncurry ($) <$> liftA2ConstCont fs xs 

||| The extension of any container with a unit shape
||| is an Naperian functor
||| Notably, lists are not applicative
public export
{l : Type} -> Naperian (Ext (Nap l)) where
  Log = l
  lookup = indexCont
  tabulate t = () <| t

||| Generalisation of 'positions' from Data.Functor
||| Works for an arbitrary container, as long as we supply its shape
||| The definition in Data.Functor.positions is for Naperian containers
||| i.e. containers with a unit shape
public export
positionsCont : {sh : c.shp} -> Ext c (c.pos sh)
positionsCont = sh <| id

--ex1 : String
--ex1 = let g = toConcreteTy $ Definition.positions {c=Vect 3} ()
--          gg = toConcreteTy $ Definition.positions {c=BinTree} (NodeS LeafS LeafS)
--          h = toConcreteTy $ Definition.positions {c=List} 4
--      in show gg

||| This states a list version of 
||| Ext c . Ext d = Ext (c . d)
public export
fromExtensionComposition : {shape : List Cont} ->
  composeExtensions shape a -> Tensor' shape a
fromExtensionComposition {shape = []} ce = MkT ce
fromExtensionComposition {shape = (c :: cs)} (sh <| contentAt) = MkT $
  let rest = GetT . fromExtensionComposition {shape=cs} . contentAt
  in (sh <| shapeExt . rest) <| \(cp ** fsh) => indexCont (rest cp) fsh

public export
toExtensionComposition : {shape : List Cont} ->
  Tensor' shape a -> composeExtensions shape a
toExtensionComposition {shape = []} (MkT t) = t
toExtensionComposition {shape = (c :: cs)} (MkT ((csh <| cpos) <| idx))
  = csh <| \d => toExtensionComposition (MkT (cpos d <| curry idx d))
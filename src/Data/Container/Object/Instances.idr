module Data.Container.Object.Instances

import Data.Vect

import Data.Container.Object.Definition
import public Data.Container.TreeUtils -- rexport all the stuff inside
import Misc

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

  ||| Isomorphic to Data.Tensor.TensorA
  ||| todo
  public export
  Tensor' : List Cont -> Type -> Type
  Tensor' cs = Ext (Tensor cs)
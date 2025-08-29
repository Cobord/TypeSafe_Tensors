module Data.Container.Object.Instances

import Data.Fin

import public Data.Container.Object.Definition
import public Data.Container.Products
import public Data.Container.TreeUtils

||| Examples that do not require any additional constraints such as Applicative
namespace MainExamples
  ||| Empty container, isomorphic to Void
  public export
  Empty : Cont
  Empty = (_ : Void) !> Void

  ||| Container with a single shape, but no positions, isomorphic to Unit : Type
  public export
  UnitCont : Cont
  UnitCont = (_ : Unit) !> Void

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
  public export
  Tensor : List Cont -> Cont
  Tensor = foldr (>@) Scalar

  ||| Cubical tensors are containers
  public export
  TensorC : List Nat -> Cont
  TensorC xs = Tensor (Vect <$> xs)

  -- TODO what is "Tensor" with hancock product? with cartesian product?
  -- with hancock product there is a duoidal structure?
  
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

  ||| Constant container, positions do not depend on shapes
  ||| Some of the above containers can be refactored in terms of these
  ||| But it's more illuminating to keep them in their raw form for now
  public export
  Const : Type -> Type -> Cont
  Const x y = (_ : x) !> y

  ||| Constant container with a single shape  
  ||| Naperian container
  public export
  Nap : Type -> Cont
  Nap x = Const Unit x


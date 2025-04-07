module Data.Container.Definition

import Data.Fin

-- Taken from Andre's code

||| A container is a product of a shape and a set of positions indexed by that shape
||| They can be used to describe data types
public export
record Container where
  constructor (!>)
  ||| Shapes
  shp : Type
  ||| Positions
  pos : shp -> Type

export typebind infixr 0 !>

%name Container c, c', c''

Tuple : (x, y : Type) -> Container
Tuple x y = (b : Bool) !> (if b then x else y)

ListCont : Container
ListCont = (n : Nat) !> (Fin n)

-- Paths
TreeCont : (x : Type) -> Container
TreeCont x = (f : List Bool) !> ?TreeCont_rhs


public export
record ContainerF where
  ||| Shapes
  shp : Type
  ||| Valuations
  R : Type
  ||| Positions
  pos : shp -> Type
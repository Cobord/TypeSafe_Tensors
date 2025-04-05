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


ListCont : Container
ListCont = (n : Nat) !> (Fin n)

-- Paths
TreeCont : Container

module Data.Container.Object.Definition

||| A container is a pair: a shape and a set of positions indexed by that shape
||| They can be used to describe various data types
public export
record Cont where
  constructor (!>)
  ||| A type of shapes
  shp : Type
  ||| For each shape, a position
  pos : shp -> Type

export typebind infixr 0 !>

%name Cont c, c', c''

||| Convenience datatype storing the property that
||| a container `c` has an interface `i` on its positions
public export
data InterfaceOnPositions : (c : Cont) -> (i : Type -> Type) -> Type where
  ||| For every shape s the set of positions c.pos s has that interface
  MkI : (p : (s : c.shp) -> i (c.pos s)) =>
    InterfaceOnPositions c i
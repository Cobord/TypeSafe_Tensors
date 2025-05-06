module Data.Container.Definition

import Data.Fin
import Data.Vect

import Data.Tree
import Data.Functor.Naperian
import Misc

%hide Data.Vect.fromList
%hide Builtin.fst

-- Inspired by Andre's code

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


Const2 : Type -> Type -> Cont
Const2 x y = (_ : x) !> y

Const : Type -> Cont
Const x = (_ : x) !> x

||| Extension of a container
||| This allows us to talk about the content, or payload of a container
public export
record Ext (c : Cont) (x : Type) where
  constructor (<|)
  shapeExt : c.shp
  indexCont : c.pos shapeExt -> x

-- public export
-- Ext : Cont -> Type -> Type
-- Ext (shp !> pos) x = (s : shp ** pos s -> x)

-- Container 'c' "full off" a type 'x'
public export
fullOf : Cont -> Type -> Type
fullOf c x = Ext c x 

-- In general hard to write Eq instance for Ext c x becuase pos is not enumerable


public export
Functor (Ext c) where
  map {c=shp !> pos} f ((s <| v)) = (s <| f . v)

liftA2ConstCont : Ext (Const2 () l) a -> Ext (Const2 () l) b -> Ext (Const2 () l) (a, b)
liftA2ConstCont (() <| va) (() <| vb) = () <| (\x => (va x, vb x))

{l : Type} -> Applicative (Ext (Const2 () l)) where
  pure a = () <| (\_ => a)
  fs <*> xs = uncurry ($) <$> liftA2ConstCont fs xs 

||| For containers where shape is Unit
||| Their extensions are Naperian
public export
{l : Type} -> Naperian (Ext ((!>) () (\_ => l))) where
  Log = l
  lookup = indexCont
  tabulate t = () <| t

-- No Applicative instance for (Ext c) in general


public export
infixr 0 ><
||| Hancock, or Dirichlet tensor product
(><) : Cont -> Cont -> Cont
(><) (shp !> pos) (shp' !> pos') = ((s, s') : (shp, shp')) !> (pos s, pos' s')
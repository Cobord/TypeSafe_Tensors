module Data.Container.Extension.Definition

import Data.Container.Object.Definition

import Data.Functor.Naperian
import Misc


||| Extension of a container
||| This allows us to talk about the content, or payload of a container
public export
record Ext (c : Cont) (x : Type) where
  constructor (<|)
  shapeExt : c.shp
  indexCont : c.pos shapeExt -> x

||| Container c can be said to be "full off" a type x
||| Sometimes used as infix operator to aid readability
||| c `fullOf` x is easier to read than Ext c x
public export
fullOf : Cont -> Type -> Type
fullOf c x = Ext c x 

||| Notably, Eq instance is not possible to write for a general Ext c a
||| This is because Eq needs to be total, and some containers have an infinite number of positions, meaning they cannot be checked in finite time
||| However, we can write ...
||| TODO do I even need this? Computing equality for general extensions is hard, and at best this piece of code can sometmes be 
namespace EqExt
  ||| Structure needed to store the equality data for Ext
  public export
  record EqExt (e1, e2 : Ext c a) where
    constructor MkEqExt
    ||| The shapes must be equal
    shapesEqual : e1.shapeExt = e2.shapeExt
    ||| For each position in that shape, the values must be equal
    ||| Relying on rewrite to get the correct type for the position
    valuesEqual : (p : c.pos (e1.shapeExt)) ->
      e1.indexCont p =
      e2.indexCont (rewrite__impl (c.pos) (sym shapesEqual) p)
    {-
    Another alternative is to use DecEq, and a different explicit rewrite
     -}

  public export
  decEqExt : (e1, e2 : Ext c a) ->
    EqExt e1 e2 ->
    Dec (e1 = e2)
  decEqExt e1 e2 (MkEqExt shapesEqual valuesEqual)
    = Yes ?decEqExt_rhs_0 -- complicated, but doable?

  
||| Every extension is a functor : Type -> Type
public export
Functor (Ext c) where
  map {c=shp !> pos} f (s <| v) = s <| f . v

||| Map preserves the shape of the extension
public export
mapShapeExt : {c : Cont} ->
  (l : c `fullOf` a) ->
  shapeExt (f <$> l) = shapeExt l
mapShapeExt {c=shp !> pos} (sh <| _) = Refl

public export
mapIndexCont : {0 f : a -> b} -> {c : Cont} ->
  (l : c `fullOf` a) ->
  (ps : c.pos (shapeExt (f <$> l))) ->
  f (indexCont l (rewrite sym (mapShapeExt {f=f} l) in ps))
    = indexCont (f <$> l) ps
mapIndexCont {c=shp !> pos} (sh <| contentAt) ps = Refl

public export
Functor ((Ext d) . (Ext c)) where
  map f e = (map f) <$> e





||| Container setter
public export
setExt : (e : Ext ((!>) sh ps) x) ->
  ((s : sh) -> Eq (ps s)) =>
  (i : ps (shapeExt e)) ->
  x ->
  Ext ((!>) sh ps) x
setExt (sh <| contentAt) i x
  = sh <| updateAt contentAt (i, x)

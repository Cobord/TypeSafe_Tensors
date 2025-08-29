module Data.Container.Products

import Data.DPair
import Decidable.Equality

import Data.Container.Object.Definition
import Data.Container.Extension.Definition

import Misc

public export infixr 0 ><
public export infixr 0 >+<
public export infixr 0 >@

||| Hancock, Dirichlet, or tensor product of containers
||| Monoid with CUnit
public export
(><) : Cont -> Cont -> Cont
(shp !> pos) >< (shp' !> pos') = ((s, s') : (shp, shp')) !> (pos s, pos' s')

||| Coproduct of containers
public export
(>+<) : Cont -> Cont -> Cont
(shp !> pos) >+< (shp' !> pos') = (es : Either shp shp') !> (case es of
  Left s => pos s
  Right s' => pos' s')

||| Composition of containers (polynomial composition)
||| Non-symmetric in general (hence why the symbol is non-symmetric too)
||| Monoid with Scalar
public export
(>@) : Cont -> Cont -> Cont
c >@ d = (ex : Ext c d.shp) !> (cp : c.pos (shapeExt ex) ** d.pos (index ex cp))


||| Derivative of a container
||| Given c=(shp !> pos) the derivative can be thought of as 
||| a shape s : shp, a distinguished position p : pos s, and the set of *all other positions*
public export
Deriv : (c : Cont) ->
  InterfaceOnPositions c DecEq =>
  Cont
Deriv (shp !> pos) @{MkI}
  = ((s ** p) : DPair shp pos) !> (p' : pos s ** IsNo (decEq p p'))
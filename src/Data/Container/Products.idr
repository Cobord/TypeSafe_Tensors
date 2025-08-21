module Data.Container.Products

import Data.DPair

import Data.Container.Object.Definition
import Data.Container.Extension.Definition


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
c >@ d = ((sh <| ind) : Ext c (d.shp)) !> (cp : c.pos sh ** d.pos (ind cp))


||| Derivative of a container
Deriv : Cont -> Cont


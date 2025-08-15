module Data.Container.Applicative.Definition

import Data.Fin
import Data.DPair

import Data.Container.Definition
import Data.Container.Morphism.Definition
import Misc

%hide Builtin.infixr.(#)

||| Applicative Container
||| Consists of a container and a proof that its extension is an applicative functor
||| Defined using Idris' auto as we'd like to avoid directly providing this
public export
record ContA where
  constructor (#)
  GetC : Cont
  ||| Question: can we state this without referencing the extension?
  {auto applPrf : Applicative (Ext GetC)}

public export prefix 0 #

||| Convenience functions so we dont have to keep writing GetC
public export
(.shp) : ContA -> Type
(.shp) c = (GetC c) .shp

public export
(.pos) : (c : ContA) -> c.shp -> Type
(.pos) c sh = (GetC c) .pos sh

||| Specialised to composition product of containers
||| We pattern match on three cases to simplify resulting expressions
public export
ComposeContainers : List ContA -> Cont
ComposeContainers [] = CUnit
ComposeContainers [c] = GetC c
ComposeContainers (c :: d :: cs) = GetC c >@< ComposeContainers (d :: cs)
-- ComposeContainers cs = foldr (>@<) CUnit (GetC <$> cs)

public export
ComposeExtensions : List ContA -> Type -> Type
ComposeExtensions [] a = Ext CUnit a
ComposeExtensions [c] a = Ext (GetC c) a
ComposeExtensions (c :: d :: cs) a
  = Ext (GetC c) (ComposeExtensions (d :: cs) a)

||| This states a list version of 
||| Ext c2 . Ext c1 = Ext (c2 . c1)
public export
toContainerComp : {conts : List ContA} ->
  ComposeExtensions conts a -> Ext (ComposeContainers conts) a
toContainerComp {conts = []} ce = ce
toContainerComp {conts = [c]} ce = ce
toContainerComp {conts = (c :: d :: cs)} (shp <| idx) = 
  let rst = (toContainerComp {conts=(d :: cs)}) . idx
  in (shp <| shapeExt . rst) <| (\(cp ** fsh) => indexCont (rst cp) fsh)

public export
fromContainerComp : {conts : List ContA} ->
  Ext (ComposeContainers conts) a -> ComposeExtensions conts a
fromContainerComp {conts = []} ce = ce
fromContainerComp {conts = [c]} ce = ce
fromContainerComp {conts = (c :: d :: cs)} ((csh <| cpos) <| idx)
  = csh <| \d => fromContainerComp (cpos d <| curry idx d)




-- public export
-- mapComposeExtensions : {conts : List ContA} ->
--   (f : a -> b) -> ComposeExtensions conts a -> ComposeExtensions conts b
-- mapComposeExtensions {conts = []} f e = f <$> e
-- mapComposeExtensions {conts = ((# c) :: cs)} f e = mapComposeExtensions f <$> e
-- 
-- public export
-- [FCE] {conts : List ContA} -> Functor (ComposeExtensions conts) where
--   map f ce = ?vnn -- mapComposeExtensions
-- 
-- testTT : {c : ContA} -> (f : String -> Int) -> ComposeExtensions [c] String -> ComposeExtensions [c] Int
-- testTT f = map @{FCE {conts=[c]}} f
-- 
-- public export
-- compExtReplicate : {conts : List ContA} ->
--   a -> ComposeExtensions conts a
-- compExtReplicate {conts = []} a = fromIdentity a
-- compExtReplicate {conts = ((#) _ {applPrf} :: _)} a
--   = compExtReplicate <$> pure a
-- 
-- public export
-- compExtLiftA2 : {conts : List ContA} ->
--   ComposeExtensions conts a ->
--   ComposeExtensions conts b ->
--   ComposeExtensions conts (a, b)
-- compExtLiftA2 {conts = []} ca cb = fromIdentity (toIdentity ca, toIdentity cb)
-- compExtLiftA2 {conts = ((#) c {applPrf} :: cs)} ca cb
--   = uncurry compExtLiftA2 <$> liftA2 ca cb


-- Tensors should eventually more and more use the container backend
-- public export
-- Applicative (ComposeExtensions conts) using FCE where
--   pure = compExtReplicate
--   fs <*> xs = uncurry ($) <$> compExtLiftA2 fs xs

-- public export
-- compReplicate : {conts : List ContA} ->
--   a -> Ext (ComposeContainers conts) a
-- compReplicate {conts = []} x = fromIdentity x
-- compReplicate {conts = (c :: cs)} x
--   = ?ff <| ?bb

-- compReplicate {conts = []} a = fromIdentity a
-- compReplicate {conts = (c :: cs)} a
--   = let (sh <| ind) = compReplicate {conts=cs} a
--     in (?ff <| ?vmm) <| ?bb
--compReplicate {conts = []} a = fromIdentity a
--compReplicate {conts = ((# c) :: cs)} a
--  = pure {f=Ext c} $ compReplicate {conts=cs} a



-- ||| Given a list of natural numbers, when we convert this to composition product of containers, this will have a unit shape
-- ||| We don't do rewrites to prove this (as it's not definitionally equal to unit shape, but only isomorphic)
-- ||| Hence, just like with EmptyExt we provide convenience functions to create this unit shape easily
-- public export
-- emptyShapeCubicalTensor : {shape : List Nat} ->
--   (ComposeContainers (Vect <$> shape)) .shp
-- emptyShapeCubicalTensor {shape = []} = ()
-- emptyShapeCubicalTensor {shape = (_ :: _)}
--   = () <| (\_ => emptyShapeCubicalTensor)

-- shapeOfCubicalTensorIsUnit : {shape : List Nat} ->
--   (ComposeContainers (Vect <$> shape)) .shp = ()
-- shapeOfCubicalTensorIsUnit {shape = []} = Refl
-- shapeOfCubicalTensorIsUnit {shape = (s :: ss)}
--   = rewrite shapeOfCubicalTensorIsUnit {shape = ss} in ?afasdf

-- public export
-- ComposeContainers' : {conts : List ContA} ->
--   ContAontList conts -> ContA
-- ComposeContainers' [] = # CUnit
-- ComposeContainers' (c :: cs) =
--   (#) (c >< prodConts (applContListToContList cs))
--     {applPrf = ?ComposeContainers_rhs_1}

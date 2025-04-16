module Tensor.GenTensor

import Data.Vect
import Data.Vect.Quantifiers

import Tensor
import Tree

%hide Builtin.infixr.(#)

||| Generalised tensors
||| For storing not necessarily cube-like structures
public export
data GenTensor : (shape : Vect n (Type -> Type)) -> (dtype : Type) -> Type where
    GTZ : (val : dtype) -> GenTensor [] dtype
    GTS : f (GenTensor ds dtype) -> GenTensor (f :: ds) dtype

%name GenTensor t, u, v

public export
data AllEq : (shape : Vect n (Type -> Type)) -> (dtype : Type) -> Type where
  NilEq : Eq a => AllEq [] a
  ConsEq : Eq (f (GenTensor fs dtype)) => AllEq (f :: fs) dtype

public export
genTensorEq : (allEq : AllEq shape a) => GenTensor shape a -> GenTensor shape a -> Bool
genTensorEq (GTZ x) (GTZ y) {allEq = NilEq} = x == y
genTensorEq (GTS xs) (GTS ys) {allEq = ConsEq} = xs == ys

(allEq : AllEq shape a) => Eq (GenTensor shape a) where
  (==) = genTensorEq

public export
data AllShow : (shape : Vect n (Type -> Type)) -> (dtype : Type) -> Type where
  NilShow : Show a => AllShow [] a
  ConsShow : Show (f (GenTensor fs dtype)) => AllShow (f :: fs) dtype

public export
genTensorShow : (allShow : AllShow shape a) => GenTensor shape a -> String
genTensorShow {allShow = NilShow} (GTZ val) = show val
genTensorShow {allShow = ConsShow} (GTS xs) = show xs

(allShow : AllShow shape a) => Show (GenTensor shape a) where
  show = genTensorShow

-- public export
-- data AllFunctor : (shape : Vect n (Type -> Type)) -> (dtype : Type) -> Type where
--   NilFunctor : AllFunctor [] a
--   ConsFunctor : Functor f => f (GenTensor fs dtype) -> AllFunctor (f :: fs) dtype
-- 
-- mapGenFunctor : (allFunctor : AllFunctor shape a) => (f : a -> b) -> GenTensor shape a -> GenTensor shape b
-- mapGenFunctor {allFunctor = NilFunctor} fn (GTZ val) = GTZ (fn val)
-- mapGenFunctor {allFunctor = (ConsFunctor ft)} fn (GTS xs)
--   = GTS (?holeFunctor <$> xs) -- (mapGenFunctor fn) works but needs to be extracted to the type level...

export prefix 0 #
||| FunctorI standing for FunctorImplicit
record Prop (prop : (Type -> Type) -> Type) where
  constructor (#)
  F : Type -> Type
  {auto 0 prf : prop F}

public export
data AllFunctor : (shape : Vect n (Prop Functor)) -> (dtype : Type) -> Type where
    NilFunctor : AllFunctor [] a
    ConsFunctor : Functor f => f (AllFunctor ds dtype) -> AllFunctor ((# f) :: ds) dtype

public export
data AllFoldable : (shape : Vect n (Prop Foldable)) -> (dtype : Type) -> Type where
    NilFoldable : AllFoldable [] a
    ConsFoldable : Foldable f => f (AllFoldable ds dtype) -> AllFoldable ((# f) :: ds) dtype


public export
getF : Vect n (Prop p) -> Vect n (Type -> Type)
getF [] = []
getF ((# f) :: fs) = f :: getF fs


mapGenTensor : (allFunctor : AllFunctor shape a) => (f : a -> b) -> GenTensor (getF shape) a -> GenTensor (getF shape) b
mapGenTensor {allFunctor = NilFunctor} f (GTZ val) = GTZ (f val)
mapGenTensor {allFunctor = (ConsFunctor x)} f (GTS xs) = GTS (?ho <$> xs)
 
(allFunctor : AllFunctor shape a) => Functor (GenTensor (getF shape)) where
  map f = ?ooo
-- (allFunctor : AllFunctor shape a) => Functor (GenTensor shape) where
--   map = mapGenFunctor
--   map {allFunctor = NilFunctor} fn (GTZ val) = GTZ (fn val)
--   map {allFunctor = (ConsFunctor _)} fn (GTS xs)
--     = GTS ((map fn) <$> xs)
-- (map fn) should work but it says it can't find an implementation for Functor (GenTensor ds)??

-- Functor (GenTensor shape) where
--   map f (GTZ val) = GTZ (f val)
--   map f (GTS xs) = GTS ((map f) <$> xs)

-- data AllFoldable : (shape : Vect n (Type -> Type)) -> (dtype : Type) -> Type where
--   NilFoldable : AllFoldable [] a
--   ConsFoldable : Foldable f => f (GenTensor fs dtype) -> AllFoldable (f :: fs) dtype
-- 
-- foldrGenFoldable : (allFoldable : AllFoldable shape a) => (f : a -> b -> b) -> (z : b) -> GenTensor shape a -> b
-- foldrGenFoldable {allFoldable = NilFoldable} f z (GTZ val) = f val z
-- foldrGenFoldable {allFoldable = (ConsFoldable ft)} f z (GTS xs) = foldr (?hole1) z xs -- \t, acc => foldr f acc t should work but same problem as in Functor. Needs to be extracted to the type level...

-- Foldable (GenTensor shape) where
--   foldr f z (GTZ val) = f val z
--   foldr f z (GTS xs) = ?loo_1
{-
-- List $ Vect n $ BinTreeLeafOnly Double
exampleGenTensor : GenTensor [# List, # Vect n, # BinTreeLeafOnly] Double
exampleGenTensor = ?exampleGenTensor_rhs


-- public export
-- {shape : Vect n (Type -> Type)} -> (allShow : AllShow shape a) => Show (GenTensor shape a) where
--   show {allShow = NilShow} (GTZ val) = show val
--   show {allShow = ConsShow @{sb}} (GTS xs) = let t = show @{sb} xs in ?show_rhs_2
--   -- show {shape = []} {allFunctor = []} {allShow = NilShow} (GTZ val) = show val
  -- show {shape = (s :: ss)} {allFunctor = (f :: fs)} {allShow = ConsShow @{sb}} (GTS xs) = let t = map {f=s} show xs in ?alalal_4
  -- -- show {allShow = NilShow} (GTZ val) = show val
  -- show {allShow = ConsShow @{ss}} (GTS t) = show (show <$> t)
-- show {shape = []} (GTZ val) = show val
-- show {shape = (f :: fs)} (GTS y) = ?all_2

public export
data AllEq : (shape : Vect n (Type -> Type))
           -> (dtype : Type)
           -> Type where
  NilEq : Eq a => AllEq [] a
  ConsEq : Eq (f (GenTensor fs dtype)) => AllEq (f :: fs) dtype

-- How do Functor and Eq interact here?
public export
{shape : Vect n (Type -> Type)} -> (allEq : AllEq shape a) => Eq (GenTensor shape a) where
  (==) (GTZ x) (GTZ y) {allEq = NilEq}  = x == y
  (==) (GTS {f} xs) (GTS {f} ys) {allEq = ConsEq @{sb}}  = ?poo_3
  -- (==) {allEq} (GTZ x) (GTZ y) = ?ooo -- x == y
  -- (GTS xs) == (GTS ys) = ?oooo_2
    -- (GTZ t) == (GTZ u) = t == u
    -- (GTS ts) == (GTS us) = ?lafl_2
preserves : {a : Type} -> (a -> Type) -> (a -> a) -> Type
preserves {a} c f = (x : a) -> (c x -> c (f x))

allShow : (shape : Vect n (Type -> Type)) -> Type
allShow shape = All (preserves Show) shape





-- findShow : AllShow shape dtype -> GenTensor shape dtype -> Show dtype
-- findShow NilShow (GTZ val) = 
-- findShow ConsShow t = ?findShow_rhs_1

-- public export
-- {shape : Vect n (Type -> Type)} -> (allShow : AllShow shape a) => Show (GenTensor shape a) where
--    show t = let xt = allShow in ?sss
--   -- show {shape = []} (GTZ val) = show val
  -- show {shape = (f :: fs)} (GTS fx) = ?asdf_2
  -- show (GTZ x) = show x
  -- show (GTS xs) = ?asdf

-- public export
-- {shape : Vect n (Type -> Type)} -> Num a => Num (GenTensor shape a) where
--   fromInteger = ?fiii
--   (+) = ?alll
--   (*) = ?loooo
public export
GenArray : (shape : Vect rank (Type -> Type)) -> (dtype : Type) -> Type
GenArray [] dtype = dtype
GenArray (s :: ss) dtype = s (GenArray ss dtype)

public export
-- fromGenArray : {shape : Vect rank (Type -> Type)} -> GenArray shape a -> GenTensor shape a
-- fromGenArray {shape = []} a = GTZ a
-- fromGenArray {shape = (_ :: _)} t = GTS (fromGenArray <$> t)


-- This recovers usual tensors in Tensor.Tensor
-- Tensor' : (shape : Vect n Nat) -> Type -> Type
-- Tensor' shape = GenTensor (Vect <$> shape)

h : Vect 2 (Type -> Type)
h = [List, Tensor [2, 3]]

t0 : GenTensor [] Double
t0 = GTZ 3

-- t1 : GenTensor [List] Double
-- t1 = GTS [GTZ 2, GTZ 3, GTZ 17]

-- t2 : GenTensor [List, Vect 2] Double
-- t2 = GTS [GTS [GTZ 14, GTZ 9]]

t3 : GenTensor [BinTreeLeafOnly, Vect 2] Double
t3 = GTS ?eoo 

-- ttt : Tensor' [3, 4] Double
-- ttt = fromArray [ [0, 1, 2, 3]
--                 , [4, 5, 6, 7]
--                 , [8, 9, 10, 11]]
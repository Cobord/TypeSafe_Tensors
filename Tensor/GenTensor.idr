module Tensor.GenTensor

import Data.Vect
import Data.Vect.Quantifiers

import Tensor
import Tree

%hide Builtin.infixr.(#)

export prefix 0 #
||| FunctorI standing for FunctorImplicit
record FunctorI where
  constructor (#)
  fff : Type -> Type
  {auto 0 prf : Functor fff}

||| Generalised tensors
||| For storing not necessarily cube-like structures
public export
data GenTensor : (shape : Vect n FunctorI) -> (dtype : Type) -> Type where
    GTZ : (val : dtype) -> GenTensor [] dtype
    GTS : Functor f => f (GenTensor ds dtype) -> GenTensor ((# f) :: ds) dtype

%name GenTensor t, u, v

public export
data AllShow : (shape : Vect n (Type -> Type)) -> (dtype : Type) -> Type where
  NilShow : Show a => AllShow [] a
  ConsShow : Show (f (GenTensor fs dtype)) => AllShow (f :: fs) dtype

Functor (GenTensor shape) where
  map f (GTZ val) = GTZ (f val)
  map f (GTS xs) = GTS ((map f) <$> xs)

Foldable (GenTensor shape) where
  foldr f z (GTZ val) = f val z
  foldr f z (GTS xs) = ?loo_1
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
  (==) (GTS xs) (GTS ys) {allEq = ConsEq @{sb}}  = ?poo_3
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
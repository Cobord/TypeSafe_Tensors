module Data.Unique

import Data.Vect
import Data.List
import Decidable.Equality
import Decidable.Equality.Core

-- Definitions of vectors/lists with unique elements

||| A proof that an element x is not found in vector xs
||| Dual of Elem
data NotElem : (x : a) -> (xs : Vect n a) -> Type where
  NotElemEmpty : NotElem x []
  NotElemCons : Eq a => {x, y : a} ->
    NotElem x xs ->
    So (x /= y) ->
    NotElem x (y :: xs)

||| A proof that some element is found in a vector at position i
||| Position-relevant variant of Elem
public export
data ElemIndex : a -> Fin n -> Vect n a -> Type where 
  Here : ElemIndex x FZ (x :: xs)
  There : (later : ElemIndex x i xs) -> ElemIndex x (FS i) (y :: xs)

data IsNo : Dec a -> Type where
  ItIsNo : {prop : Type} -> {contra : Not prop} -> IsNo (No contra)

ff : DecEq a => {x : a} -> IsNo (decEq x x) -> Void
ff y = ?ff_rhs

-- fff : {a : Type} -> DecEq a => {x, y : a} -> (neq : Not (x = y)) -> IsNo (decEq x y)
-- fff neq = ItIsNo {prop=(x = y)} {contra=(neq)}



mutual
  ||| A list with unique elements
  ||| Constructively defined, an element can be inserted if it is not already in the list
  data UniqueList : (a : Type) -> Type where
    Nil : {a : Type} -> UniqueList a
    (::) : {a : Type} ->
      (x : a) ->
      (xs : UniqueList a) ->
      {auto prf : NotElemUnique x xs} ->
      UniqueList a

  ||| A proof that an element x is not found in the UniqueList xs
  data NotElemUnique : {a : Type} ->
    (x : a) -> (xs : UniqueList a) -> Type where
    NotInEmptyList : {a : Type} -> DecEq a => (x : a)
      -> NotElemUnique {a=a} x []
    NotInNonEmptyList : {a : Type} -> DecEq a =>
      {x, y : a} ->
      (xs : UniqueList a) ->
      NotElemUnique x xs ->
      {auto neq : IsNo (decEq x y)} ->
      {auto prf : NotElemUnique y xs} ->
      NotElemUnique x (y :: xs)

  ||| Decide if an element is found or not in a UniqueList
  isElemInUniqueList : {a : Type} -> DecEq a =>
    (x : a) -> (xs : UniqueList a) -> Dec (NotElemUnique x xs)
  isElemInUniqueList x [] = Yes (NotInEmptyList x)
  isElemInUniqueList x (y :: xs) = case decEq x y of
    Yes Refl => No (\p => case p of 
      (NotInNonEmptyList _ _ {neq}) => ?nnn) -- neq Refl)
    No neq => case isElemInUniqueList x xs of
      Yes prf => Yes (NotInNonEmptyList _ prf {neq=(?iii)})
      No nprf => No (\p => case p of
        NotInNonEmptyList _ prf' => nprf prf')

  fromVect : {a : Type} -> DecEq a => Vect n a -> UniqueList a
  fromVect [] = []
  fromVect (x :: xs) = case isElemInUniqueList x (fromVect xs) of
    Yes pp => x :: fromVect xs
    No _ => fromVect xs

av : UniqueList Nat
av = [1, 2, 3]

avv : UniqueList Nat
avv = fromVect [1, 2, 3, 3]

-- ||| A vector of unique elements
-- ||| Consists of a vector and a proof that once we remove duplicates, we get the same vector back
-- public export
-- record UniqueVect (n : Nat) (a : Type) {auto eq : Eq a} where
--    constructor MkUniqueVect
--    baseVect : Vect n a
--    isUnique: nub baseVect = baseVect

module Data.Unique

import Data.Vect
import Data.List
import Decidable.Equality
import Decidable.Equality.Core
import Data.List.Elem

||| Proofs about elements existing or not existing in vectors
namespace ElemVector
  ||| A proof that some element is found in a vector at position i
  ||| Position-relevant variant of Elem
  public export
  data ElemIndex : a -> Fin n -> Vect n a -> Type where 
    Here : ElemIndex x FZ (x :: xs)
    There : (later : ElemIndex x i xs) -> ElemIndex x (FS i) (y :: xs)


  ||| A proof that an element x is not found in vector xs
  ||| Dual of Elem
  data NotElem : (x : a) -> (xs : Vect n a) -> Type where
    NotElemEmpty : NotElem x []
    NotElemCons : Eq a => {x, y : a} ->
      NotElem x xs ->
      So (x /= y) ->
      NotElem x (y :: xs)



public export
data IsNo : Dec a -> Type where
  ItIsNo : {prop : Type} -> {contra : Not prop} -> IsNo (No {prop=prop} contra)


public export
[uniqueUninhabited] {a : Type} -> {x : a} -> (de : DecEq a) =>
Uninhabited (IsNo (Equality.decEq x x)) where
  uninhabited y with (decEq x x)
    _ | (Yes prf) with (y)
      _ | (ItIsNo _) impossible
    _ | (No contra) = contra Refl


||| Proof of inequality yields IsNo
public export
proofIneqIsNo : {x, y : a} -> DecEq a => ((x = y) -> Void) -> (IsNo (Equality.decEq x y))
proofIneqIsNo f with (decEq x y)
  _ | (Yes prf) = absurd (f prf)
  _ | (No contra) = ItIsNo


-- Definitions of vectors/lists with unique elements


mutual
  ||| A list with unique elements
  ||| An element can be inserted if it is not already in the list
  ||| Like a Set, but with ordering
  public export
  data UniqueList : (a : Type) -> DecEq a => Type where
    Nil : {a : Type} -> DecEq a => UniqueList a
    (::) : {a : Type} -> DecEq a =>
      (x : a) ->
      (xs : UniqueList a) ->
      {auto prf : NotElem x xs} ->
      UniqueList a

  ||| A proof that an element x is not found in the UniqueList xs
  public export
  data NotElem : {a : Type} -> DecEq a =>
    (x : a) -> (xs : UniqueList a) -> Type where
    NotInEmptyList : {a : Type} -> DecEq a => (x : a)
      -> NotElem {a=a} x []
    NotInNonEmptyList : {a : Type} -> (de : DecEq a) =>
      {x, y : a} ->
      (xs : UniqueList a) ->
      NotElem x xs ->
      {auto neq : IsNo (decEq x y)} ->
      {auto prf : NotElem y xs} ->
      NotElem x (y :: xs)


||| Decision procedure for proving an element is not found in an UniqueList
public export
decElemNotInUniqueList : {a : Type} -> DecEq a =>
  (x : a) -> (xs : UniqueList a) -> Dec (NotElem x xs)
decElemNotInUniqueList x [] = Yes (NotInEmptyList x)
decElemNotInUniqueList x (y :: xs) = case decEq x y of
  Yes Refl => No (\p => case p of -- x is equal to y, we already know the answer is No then
    (NotInNonEmptyList {de} _ _ {neq}) => uninhabited @{uniqueUninhabited {de=de}} neq) 
  No neq => case decElemNotInUniqueList x xs of -- we have to check the rest
    Yes prf => Yes (NotInNonEmptyList _ prf {neq=(proofIneqIsNo neq)})
    No nprf => No (\p => case p of
      NotInNonEmptyList _ prf' => nprf prf')

public export
toList : {a : Type} -> DecEq a => UniqueList a -> List a
toList [] = []
toList (x :: xs) = x :: toList xs

public export
fromList : {a : Type} -> DecEq a => List a -> UniqueList a
fromList [] = []
fromList (x :: xs) = case decElemNotInUniqueList x (fromList xs) of
  Yes _ => x :: fromList xs
  No _ => fromList xs

public export
fromVect : {a : Type} -> DecEq a => Vect n a -> UniqueList a
fromVect [] = []
fromVect (x :: xs) = case decElemNotInUniqueList x (fromVect xs) of
  Yes _ => x :: fromVect xs
  No _ => fromVect xs

public export
toVect : {a : Type} -> DecEq a => UniqueList a -> (n : Nat ** Vect n a)
toVect [] = (0 ** [])
toVect (x :: xs) = let (n ** xs) = toVect xs
                   in (S n ** x :: xs)


namespace UniqueListConcat
  {-
  Concatenation of unique lists
  Needs to be in a mutual block with expandUnique
   -}
  public export infixr 5 +++
  public export
  (+++) : {a : Type} -> DecEq a =>
    (xs, ys : UniqueList a) -> UniqueList a

  public export
  expandUnique : {a : Type} -> DecEq a =>
    (x' : a) ->
    (xs, ys : UniqueList a) ->
    {prfx : NotElem x' xs} ->
    {prfy : NotElem x' ys} ->
    NotElem x' (xs +++ ys)

  (+++) [] ys = ys
  (+++) ((::) x xs {prf=prfx}) ys = case decElemNotInUniqueList x ys of
    Yes prfy_x => (::) x (xs +++ ys) {prf=(expandUnique x xs ys {prfx=prfx} {prfy=prfy_x})}
    No _ => xs +++ ys

  expandUnique x' [] ys {prfy} = prfy
  expandUnique x' ((::) x xs {prf=not_elem_x_xs}) ys
    {prfx = (NotInNonEmptyList {neq} xs not_elem_x'_xs)}
    {prfy=not_elem_x'_ys} with (decElemNotInUniqueList x ys)
    _ | (Yes _)
      = let v = expandUnique x' xs ys {prfx=not_elem_x'_xs} {prfy=not_elem_x'_ys}
        in NotInNonEmptyList {x=x'} {y=x} (xs +++ ys) v {neq} {prf=(expandUnique x xs ys)}
    _ | (No _)
      = expandUnique x' xs ys {prfx=not_elem_x'_xs} {prfy=not_elem_x'_ys}

      -- let prfx_tail = case prfx of
      --                   NotInNonEmptyList _ prfx_tail => prfx_tail
      --     neq_x'_x = case prfx of
      --                  NotInNonEmptyList {neq} _ _ => neq
      -- in NotInNonEmptyList (xs +++ ys) (expandUnique x' xs ys {prfx=prfx_tail} {prfy=prfy}) {neq=neq_x'_x}
      -- let prfx_tail = case prfx of
      --                   NotInNonEmptyList _ prfx_tail => prfx_tail
      -- in expandUnique x' xs ys {prfx=prfx_tail} {prfy=prfy}


concatMapUnique : {a : Type} -> DecEq a =>
  List (UniqueList a) -> UniqueList a
concatMapUnique [] = []
concatMapUnique (x :: xs) = x +++ concatMapUnique xs


namespace All
  ||| A proof that all elements of a unique list satisfy a property. 
  public export
  data All : (0 p : a -> Type) -> DecEq a => UniqueList a -> Type where
    Nil  : {a : Type} -> {0 p : a -> Type} -> DecEq a => All p Nil
    (::) : {a : Type} -> DecEq a =>
      {0 p : a -> Type} ->
      {x : a} ->
      {0 xs : UniqueList a} ->
      {auto prf : NotElem x xs} ->
      p x ->
      All p xs ->
      All p (x :: xs)


av : UniqueList Nat
av = [1, 2, 3]

as : UniqueList String
as = ["a", "b", "c", "ieva"]

avv : UniqueList Nat
avv = fromVect [1, 2, 3, 3]

namespace UniqueListFrom
  ||| A list of unique elements with elements from ls
  public export
  data UniqueListFrom : (a : Type) -> (ls : List a) -> Type where
    MkUniqueListFrom : {a : Type} -> DecEq a => {ls : List a} ->
      (xs : UniqueList a) -> {auto prf : All (\x => Elem x ls) xs} ->
      UniqueListFrom a ls

aa : UniqueListFrom Nat [10, 11, 12]
aa = MkUniqueListFrom [10, 11]

at : UniqueList Nat
at = fromList [10, 11]

bb : UniqueListFrom Char ['a', 'b', 'c']
bb = MkUniqueListFrom ['a', 'b']

packUnique : UniqueList Char -> String
packUnique = pack . toList

unpackUnique : String -> UniqueList Char
unpackUnique = fromList . unpack

public export
data UniqueString : Type where
  MkUniqueString : (str : String) ->
    {auto prf : packUnique (unpackUnique str) = str} ->
    UniqueString

public export
data UniqueStringFrom : (alphabet : String) -> Type where
  MkUniqueStringFrom : {alphabet : String} ->
     (str : String) ->
     {auto prf : packUnique (unpackUnique str) = str} ->
     {auto prf22 : All (\c => Elem c (unpack alphabet)) (unpackUnique str)} ->
     UniqueStringFrom alphabet

ttfrom : UniqueStringFrom "ijk"
ttfrom = MkUniqueStringFrom "ijk"


-- ||| A vector of unique elements
-- ||| Consists of a vector and a proof that once we remove duplicates, we get the same vector back
-- public export
-- record UniqueVect (n : Nat) (a : Type) {auto eq : Eq a} where
--    constructor MkUniqueVect
--    baseVect : Vect n a
--    isUnique: nub baseVect = baseVect

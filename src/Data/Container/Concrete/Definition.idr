module Data.Container.Concrete.Definition

import Data.Container.Object.Definition
import Data.Container.Extension.Definition

||| Idris already has concrete implementations of many containers 
||| we're interested in, and often for concrete instantiations of 
||| various container types it's useful to be able to do it using 
||| the Idris instance
public export
interface FromConcrete (cont : Cont) where
  constructor MkConcrete
  concreteType : Type -> Type
  concreteFunctor : Functor concreteType
  fromConcreteTy : concreteType a -> Ext cont a
  toConcreteTy : Ext cont a -> concreteType a
  
  
public export
data AllConcrete : List Cont -> Type where
  Nil : AllConcrete []
  Cons : (firstConcrete : FromConcrete c) =>
    (restConcrete : AllConcrete cs) =>
    AllConcrete (c :: cs)


-- public export
-- fromConcreteMap : {cont1, cont2 : Cont} ->
--   (fc1 : FromConcrete cont1) => (fc2 : FromConcrete cont2) =>
--   (concreteType @{fc1} a -> concreteType @{fc2} b) ->
--   cont1 `fullOf` a -> cont2 `fullOf` b
-- fromConcreteMap f = fromConcrete @{fc2} . f . toConcrete @{fc1}

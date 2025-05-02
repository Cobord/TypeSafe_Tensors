module Data.Rig

import Data.Vect

import Misc

-- We're also interested in natural numbers as an example
public export
interface Rig a where
  constructor MkRig
  zero : a
  one : a
  (~+~) : a -> a -> a
  (~*~) : a -> a -> a
  -- also laws, but we don't care right now

export infixr 6 ~+~
export infixr 7 ~*~

public export
Num a => Rig a where
  zero = fromInteger 0
  one = fromInteger 1
  (~+~) = (+)
  (~*~) = (*)

||| Pointwise Rig structure for Applicative functors
public export
[applicativeRig] Rig a => Applicative f => Rig (f a) where
  zero = pure zero
  one = pure one
  xs ~+~ ys = uncurry (~+~) <$> liftA2 xs ys
  xs ~*~ ys = uncurry (~*~) <$> liftA2 xs ys

public export
sum : Rig a => Vect n a -> a
sum = foldr (~+~) zero

public export
prod : Rig a => Vect n a -> a
prod = foldr (~*~) one
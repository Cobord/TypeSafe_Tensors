module Data.Container.SubTerm



||| Like Ord, but that can fail
||| Used to compare whether a term is a subterm of another term
||| Or it can be thought of as computing subpaths in a tree
||| This sounds like something that should be generally possible to derive
||| with metaprogramming for any inductive type?
||| In general, there is probably a better way to do this?
||| I could imagine this being a built in functionality in a functional language
public export
interface Eq a => MOrd a where
  mcompare : a -> a -> Maybe Ordering

public export
Ord a => MOrd a where
  mcompare x y = Just $ compare x y

public export
isSubTerm : MOrd a => a -> a -> Bool
isSubTerm x y = case mcompare x y of
  Just LT => True
  _ => False
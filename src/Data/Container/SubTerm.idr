module Data.Container.SubTerm

-- temporary experimentation

||| Like Ord, but with a comparison that can fail
||| Can be thought of as computing whether a term is a subterm of another term,
||| or as computing common prefixes/subpaths in a tree
public export
interface Eq a => MOrd a where
  constructor MkMOrd
  mcompare : a -> a -> Maybe Ordering

public export
Ord a => MOrd a where
  mcompare x y = Just $ compare x y

public export
isSubTerm : MOrd a => a -> a -> Bool
isSubTerm x y = case mcompare x y of
  Just LT => True
  _ => False

-- ||| Should generally be possible to derive with metaprogramming
-- ||| This sounds like something that should be generally possible to derive
-- ||| with metaprogramming for any inductive type?
-- ||| I could imagine this being a built in functionality in a functional language
module Data.Tensor.Einsum

import Data.Vect
import Data.List
import Data.List1
import Data.HashMap
import Data.String.Parser
import Decidable.Equality
-- import Data.List.Elem

import Data.Unique
import Data.Tensor.Tensor
import Data.Tensor.NaperianTensor
import Misc

{-
----------------------------------------
----- Docs:
----------------------------------------
Einstein Summation in Numpy: https://obilaniu6266h16.wordpress.com/2016/02/04/einstein-summation-in-numpy/
as_strided and sum is all you need: https://jott.live/markdown/as_strided
Basic guide to einsum: https://ajcr.net/Basic-guide-to-einsum/
Named Tensor Notation: https://arxiv.org/abs/2102.13196
Functional Einsum: https://www.cambridge.org/core/journals/journal-of-functional-programming/article/domainspecific-tensor-languages/19B95794B66C66E117DFCFC7A21E22D5
Optimal tensor contraction: https://docs.pytorch.org/docs/stable/generated/torch.einsum.html

----------------------------------------
----- Einsum examples:
----------------------------------------
Transpose -> einsum("ij->ji")
Sum -> einsum("ij->") (equals to a fold!)
Column sum -> einsum("ij->j") 
Row sum -> einsum("ij->i")
Matrix-vector product -> einsum("ij,j->i")
Matrix-matrix product -> einsum("ij,jk->ik")
Dot product (Vector) -> einsum("i,i->")
Dot product (Matrix) -> einsum("ij,ij->")
Outer product -> einsum("i,j->ij")

x : Tensor [3, 3, 3] Double
Einsum "iii->i" x = view main diagonal
Einsum "iii->" x = trace (sum elements along diagonal)
Einsum "ijk->" x = sum all elements
Einsum "ijk->kji" x = transpose first and last axis

y : Tensor [3, 4] Double
Einsum "ii->" x = Invalid -> x is not of the right type
Einsum "ii->ii", x = Invalid -> output subscript included multiple times

Errors:
* Output subscript can't be included multiple times!
* Every output subscript has to appear in the input


----------------------------------------
----- Interface requirements
----------------------------------------
 Einsum seems to be formed out of a few operations:
 - Transpose -> Covered by Naperian
 - Sum -> Covered by Algebra
 - Dot product -> Covered by Applicative
 - Outer product -> ?
 - anything else?

----------------------------------------
----- Misc thoughts:
----------------------------------------

TODO perhaps we need Traversables to define Einsum for loops??
Traversable connection to Applicative:
https://x.com/khoiiiind/status/1925526689339379832

Product distributes over sum
Traversable distributes over Applicative


Is einsum abount binding?
 einsum("ij,jk->ik", M, N)

 Here we bind the tensor M to ij, and N to jk

Q: SCOPING: Why should scoping of Einsum names be local?
Should it perhaps be global instead?

Maybe it doesn't matter that we have Einsum "ii" (Tensor [3, 4] a),
perhaps if we want to contract, 3 and 4 should...what? be the same variable?


Should einsum work for generalised tensors?
----------------------------------------
----- Einsum algorithm:
----------------------------------------
In this example, fix:
shapeX = [100, 4, 5]
shapeY = [100, 5, 6]
x : Tensor shapeX Double
y : Tensor shapeY Double
Einsum "bij,bjk->ik" x y

Step 1: Parsing, variable binding, and error checking
We want to first collect all the unique axis names 'b', 'i', 'j', 'l' and store tham as a axisNames : UniqueVect m AxisName

So we want
"b" -> shapeX[0], shapeY[0]
"i" -> shapeX[1]
"j" -> shapeX[2], shapeY[1]
"k" -> shapeY[2]

AxisName -> List (xs : Vect n Nat, Fin n)

This is the part where we also check for errors, and inconsistent axis naming

Step 2) When we have this, there are many tensors we can get out, depending on what the output string and output tensor is




We onlOnly look at the input string and shapes, i.e. "bij,bjk" shapeX shapeY
and use it to do parsing/error checking, and performing of variable binding.


TODO What do we do about ellipsis?

Ellipsis can either be
a) on the left side of each term
b) on the right side of each term
c) in the middle, in the case of a trace (einsum("i...i->...i", x))? (todo think about this)

To enable and control broadcasting, use an ellipsis. Default NumPy-style broadcasting is done by adding an ellipsis to the left of each term, like np.einsum('...ii->...i', a). np.einsum('...i->...', a) is like np.sum(a, axis=-1) for array a of any shape. To take the trace along the first and last axes, you can do np.einsum('i...i', a), or to do a matrix-matrix product with the left-most indices instead of rightmost, one can do np.einsum('ij...,jk...->ik...', a, b).
 -}

public export
uniqueLabels : {a : Type} -> DecEq a => List (List a) -> UniqueList a
uniqueLabels [] = []
uniqueLabels (xs :: xss) = fromList xs +++ uniqueLabels xss

||| Correct by construction Einsum expression
||| Ensures that
||| a) each output label has appeared in the input
||| b) each output label appears only once
public export
data EinsumExpr : (a : Type) -> DecEq a => Type where
  Einsum : {a : Type} -> DecEq a =>
    (inputTy : List (List a)) ->
    (outputTy : UniqueList a) ->
    {auto prf : All (\x => Elem x (toList (uniqueLabels inputTy))) outputTy} ->
    EinsumExpr a


namespace EinsumToString
  ||| If a=Char, we write it as a string
  ||| Anything else we add commas between elements and brackets around
  labelToString : {a : Type} -> DecEq a => Show a => List a -> String
  labelToString {a=Char} xs = pack xs
  labelToString xs
    = let inter = case a of
            String => xs -- necessary so extra quotes aren't added
            _ => show <$> xs
      in "[" ++ concat (intersperse "," inter)  ++ "]"
  
  public export
  inputToString : {a : Type} -> DecEq a => Show a =>
    (inputTy : List (List a)) -> String
  inputToString inputTy = concat $ intersperse "," (labelToString <$> inputTy)
  
  
  public export
  outputToString : {a : Type} -> DecEq a => Show a =>
    UniqueList a -> String
  outputToString = labelToString . toList
  
  public export
  toString : DecEq a => Show a => EinsumExpr a -> String
  toString (Einsum inputTy outputTy)
    = (inputToString inputTy) ++ "->" ++ (outputToString outputTy)


oo : EinsumExpr String
oo = Einsum [["i", "j"], ["j", "k"]] ["i", "k"]

ooChar : EinsumExpr Char
ooChar = Einsum [['i', 'j'], ['j', 'k']] ['i', 'k']

uniqueLabelsVect : {nInputs : Nat} -> Vect nInputs String -> UniqueList Char
uniqueLabelsVect xs = uniqueLabels $ (unpack <$>) (toList xs)
-- uniqueLabelsVect xs = uniqueLabels (map unpack xs)

data EinsumStrExpr : Type where
  EinsumChar : (einsumExpr : String) ->
    {left, right : String} ->
    {auto prf : splitString einsumExpr "->" = (2 ** [left, right])} ->
    {nInputs : Nat} ->
    {xs : Vect nInputs String} ->
    {auto prf_left : splitString left "," = (nInputs ** xs)} ->
    {outputTy : UniqueList Char} ->
    {auto prf_unique : fromListMaybe (unpack right) = Just outputTy} ->
    {auto prf_from_input : All (\x => Elem x (toList (uniqueLabelsVect xs))) outputTy} ->
    EinsumStrExpr

esTest : EinsumStrExpr 
esTest = EinsumChar "ij,jk->ik"
    
----------------------------------------
----- String-based einsum
----------------------------------------

data EinsumParseError : Type where
  MissingArrow : EinsumParseError
  MissingComma : EinsumParseError
  InvalidTerm : EinsumParseError
  EmptyInput : EinsumParseError
  MultipleArrows : EinsumParseError
  ContentBothSidesArrow : EinsumParseError

||| This parses 
parseEinsumInput : String -> Either EinsumParseError (EinsumExpr Char)
parseEinsumInput str = case splitString "->" str of
  (0 ** _) => Left MissingArrow  -- Technically impossible
  (1 ** _) => Left ContentBothSidesArrow 
  (2 ** [left, right]) => let xs = snd (splitString left ",")
                          in ?hoole
  (_ ** xs) => Left MultipleArrows
-- parseEinsumInput input = case toList (snd (splitString input ",")) of
--   [] => Left MissingComma -- technically impossible
--   term :: terms => let inputLabels = fromList (unpack term)
--                    in Right (fromVect inputLabels ** SingleTy inputLabels)
  -- terms) => Right ?hoole -- Right (left, n, right)

||| The name for an axis is an arbitrary string, usually a single character
AxisName : Type
AxisName = String

AxisBinding : Type
AxisBinding = HashMap AxisName Nat

{-
-- case splitString input "->" of
--   (0 ** _) => Left MissingArrow -- technically impossible
--   (1 ** _) => Left MissingArrow
--   (2 ** [left, right]) => case splitString left "," of
--     (0 ** []) => let t = SingleTy {a=Char} []
--                  in Right ?hole -- Left MissingComma -- technically impossible
--     (1 ** [term]) => let inputLabels = fromList (unpack term)
--                          t = SingleTy inputLabels
--                      in Right (fromVect inputLabels ** (t ** OutputTy (MkUniqueListFrom ?loo)))
--     (n ** _) => ?hoole -- Right (left, n, right)
--   (_ ** _) => Left MultipleArrows


  -- if length input == 0
  --   then Left EmptyInput
  --   else
  --     let arrowCount = length (filter (isInfixOf (unpack "->")) (tails (unpack input)))
  --     in if arrowCount == 0
  --          then Left MissingArrow
  --          else if arrowCount > 1
  --            then Left MultipleArrows
  --            else
  --              -- Try to parse the full structure
  --              case parse einsumParser input of
  --                Left err => 
  --                  -- Try to determine what specifically went wrong
  --                  case parse leftSideParser input of
  --                    Left _ => Left InvalidTerm  -- Left side has invalid terms
  --                    Right _ => 
  --                      -- Left side is OK, check if arrow parsing works
  --                      case parse (leftSideParser *> string "->") input of
  --                        Left _ => Left MissingArrow  -- Arrow missing or malformed
  --                        Right _ => Left InvalidTerm  -- Right side must be invalid
  --                Right _ => Right input
  -- where
  --   term : Parser String
  --   term = takeWhile1 isAlpha <?> "alphabetic term"
  --   
  --   leftSideParser : Parser ()
  --   leftSideParser = ignore $ sepBy1 term (char ',') <?> "comma-separated terms"
  --   
  --   rightSideParser : Parser ()
  --   rightSideParser = ignore $ optional term <?> "optional output term"
  --   
  --   einsumParser : Parser ()
  --   einsumParser = do
  --     leftSideParser
  --     ignore $ string "->" <?> "arrow"
  --     rightSideParser
  --     eos <?> "end of input"

{-
-- Test examples
test1 : Either EinsumParseError String
test1 = parseEinsumString "ij,jk->ik"  -- Should succeed

test2 : Either EinsumParseError String  
test2 = parseEinsumString "ijk->"      -- Should succeed (sum operation)

test3 : Either EinsumParseError String
test3 = parseEinsumString "i,j->ij"    -- Should succeed (outer product)

test4 : Either EinsumParseError String
test4 = parseEinsumString "invalid"    -- Should fail with MissingArrow

test5 : Either EinsumParseError String
test5 = parseEinsumString ""           -- Should fail with EmptyInput

test6 : Either EinsumParseError String
test6 = parseEinsumString "123,456->789"  -- Should fail with InvalidTerm (non-alphabetic)

test7 : Either EinsumParseError String
test7 = parseEinsumString "i,,j->ij"   -- Should fail with InvalidTerm (empty term)

test8 : Either EinsumParseError String
test8 = parseEinsumString "i,j->123"   -- Should fail with InvalidTerm (non-alphabetic output)

test9 : Either EinsumParseError String
test9 = parseEinsumString "i->j->k"    -- Should fail with MultipleArrows

aa : String
aa = "asdf"
-}
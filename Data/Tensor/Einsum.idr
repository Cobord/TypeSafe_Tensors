module Data.Tensor.Einsum

import public Data.Vect
import public Data.List
import Decidable.Equality
-- import Data.HashMap
-- import Data.List.Elem
import Data.String

import public Data.Unique
import Data.Tensor.Tensor
import Data.Tensor.NaperianTensor
import Misc
import Language.Reflection

%language ElabReflection

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
  MkEinsumExpr : {a : Type} -> DecEq a =>
    (inputTy : List (List a)) ->
    (outputTy : UniqueList a) ->
    {auto prf : All (\x => Elem x (toList (uniqueLabels inputTy))) outputTy} ->
    EinsumExpr a


namespace EinsumToString
  ||| If a=Char, we write it as a string
  ||| Anything else we add commas between elements and brackets around
  public export
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
  toString (MkEinsumExpr inputTy outputTy)
    = (inputToString inputTy) ++ "->" ++ (outputToString outputTy)


oo : EinsumExpr String
oo = MkEinsumExpr [["i", "j"], ["j", "k"]] ["i", "k"]

ooChar : EinsumExpr Char
ooChar = MkEinsumExpr [['i', 'j'], ['j', 'k']] ['i', 'k']


----------------------------------------
----- String-based einsum
----------------------------------------

public export
data EinsumParseError : Type where
  EmptyInput : EinsumParseError
  MissingArrow : EinsumParseError
  ContentBothSidesArrow : EinsumParseError
  DuplicateOutputAxis : EinsumParseError
  OutputAxisNotInInput : EinsumParseError
  MultipleArrows : EinsumParseError

public export
Show EinsumParseError where
  show EmptyInput = "Empty input string"
  show MissingArrow = "Missing '->' arrow"
  show ContentBothSidesArrow = "Content missing on one side of arrow"
  show DuplicateOutputAxis = "Duplicate axis in output"
  show OutputAxisNotInInput = "Output axis not found in input"
  show MultipleArrows = "Multiple '->' arrows found"

||| This parses into EinsumExpr Char, but other options are also possible
||| For instance, one where we use the syntax
||| "[batch,input],[input,output]->[batch,output]"
public export
parseEinsumString : String -> Either EinsumParseError (EinsumExpr Char)
parseEinsumString str = case str of
  "" => Left EmptyInput
  _ => case splitString str "->" of
    (0 ** _) => Left MissingArrow  -- Technically impossible
    (1 ** _) => Left ContentBothSidesArrow 
    (2 ** [left, right]) => 
      let xs : Vect _ String := snd (splitString left ",")
          inputLabels : List (List Char) := unpack <$> (toList xs)
      in case fromListMaybe (unpack right) of
           Nothing => Left DuplicateOutputAxis
           Just outputTy => 
             case checkAllInInput outputTy (uniqueLabels inputLabels) of
                  Nothing => Left OutputAxisNotInInput
                  Just prf => Right (MkEinsumExpr inputLabels outputTy {prf = prf})
    (_ ** _) => Left MultipleArrows
  where
    -- Helper function to check if all output labels appear in input labels and provide proof
    checkAllInInput : (outputTy : UniqueList Char) ->
      (inputChars : UniqueList Char) -> 
      Maybe (All (\x => Elem x (toList inputChars)) outputTy)
    checkAllInInput [] inputChars = Just []
    checkAllInInput (x :: xs) inputChars = 
      case isElem x (toList inputChars) of
        Yes prf => case checkAllInInput xs inputChars of
                     Just restPrf => Just (prf :: restPrf)
                     Nothing => Nothing
        No _ => Nothing

public export
uniqueLabelsVect : {nInputs : Nat} -> Vect nInputs String -> UniqueList Char
uniqueLabelsVect xs = uniqueLabels $ (unpack <$>) (toList xs)

data EinsumStrExpr' : Type where
  EinsumChar' : (einsumExpr : String) ->
    {left, right : String} ->
    {auto prf : splitString einsumExpr "->" = (2 ** [left, right])} ->
    {nInputs : Nat} ->
    {xs : Vect nInputs String} ->
    {auto prf_left : splitString left "," = (nInputs ** xs)} ->
    {outputTy : UniqueList Char} ->
    {auto prf_unique : fromListMaybe (unpack right) = Just outputTy} ->
    {auto prf_from_input : All (\x => Elem x (toList (uniqueLabelsVect xs))) outputTy} ->
    EinsumStrExpr'


public export
data EinsumStrExpr : Type where
  EinsumChar : (einsumExprString : String) ->
    {einsumExpr : EinsumExpr Char} ->
    {auto prf : parseEinsumString einsumExprString = Right einsumExpr} ->
    EinsumStrExpr

public export
fromString : (einsumExprString : String) ->
  {einsumExpr : EinsumExpr Char} ->
  {auto prf : parseEinsumString einsumExprString = Right einsumExpr} ->
  EinsumStrExpr
fromString einsumExprString = EinsumChar einsumExprString


esTest : EinsumStrExpr 
esTest = EinsumChar "ij,jk->ik"
    
esTest' : EinsumStrExpr'
esTest' = EinsumChar' "ij,jk->ik"

-- This will only be the input
public export
data Einsum : (str : EinsumStrExpr) -> Type where
  Contract : {a : Type} ->
    {str : EinsumStrExpr} ->
    (xs : List (shape : Vect n Nat ** Tensor' shape a)) ->
    Einsum str

t1 : Tensor' [2, 3] Double
t1 = fromArray' [ [1, 2, 3], [4, 5, 6] ]

t2 : Tensor' [3, 4] Double
t2 = fromArray' [ [1, 2, 3, 4], [5, 6, 7, 8], [9, 10, 11, 12] ]

t3 : Einsum "ij,jk->ik"
t3 = Contract ?loo

tO : {i, j, k : Nat} -> Tensor' [i, j] a -> Tensor' [j, k] a -> Tensor' [i, k] a


||| The name for an axis is an arbitrary string, usually a single character
AxisName : Type
AxisName = String

-- AxisBinding : Type
-- AxisBinding = HashMap AxisName Nat

-- emptyH : AxisBinding
-- emptyH = empty

-- TODO be explciit about which errors should show up

----------------------------------------
----- Elaborator Reflection for Einsum Function Generation
----------------------------------------

-- Helper function to convert Char to variable name
charToVarName : Char -> Name
charToVarName c = UN (Basic (singleton c))

-- Generate [i, j, k] from ['i', 'j', 'k']
generateShapeVect : List Char -> TTImp
generateShapeVect [] = `([])
generateShapeVect (x :: xs) = 
  `(~(IVar EmptyFC (charToVarName x)) :: ~(generateShapeVect xs))

-- Generate Tensor' [i, j] a from shape ['i', 'j']
generateTensorType : List Char -> TTImp
generateTensorType shape = 
  let shapeVect = generateShapeVect shape
  in `(Tensor' ~(shapeVect) a)

-- Build function type with implicit Nat parameters and explicit tensor parameters
buildEinsumFunctionType : List Char -> List (List Char) -> List Char -> TTImp
buildEinsumFunctionType uniqueVars inputShapes outputShape =
  let
    inputTensorTypes : List TTImp := generateTensorType <$> inputShapes
    outputTensorType : TTImp := generateTensorType outputShape
    
    -- Build the main function type: input1 -> input2 -> ... -> output
    mainFunctionType : TTImp := foldr (\inputType, acc =>
      IPi EmptyFC MW ExplicitArg Nothing inputType acc)
      outputTensorType inputTensorTypes
    
    -- Add implicit {i, j, k : Nat} parameters
    withNatParams : TTImp := foldr (\var, acc => 
      IPi EmptyFC MW ImplicitArg (Just (charToVarName var)) `(Nat) acc) mainFunctionType uniqueVars
    
    -- Add implicit {a : Type} parameter FIRST (before the Nat parameters)
    fullType : TTImp := IPi EmptyFC MW ImplicitArg (Just (UN (Basic "a"))) `(Type) withNatParams
    
  in fullType

-- Simple string replacement function
replaceString : String -> String -> String -> String
replaceString old new str = 
  let chars = unpack str
      oldChars = unpack old
      newChars = unpack new
  in pack (replaceInList oldChars newChars chars)
  where
    replaceInList : List Char -> List Char -> List Char -> List Char
    replaceInList [] _ xs = xs
    replaceInList old new [] = []
    replaceInList old new xs@(x :: rest) =
      if isPrefixOf old xs
        then new ++ replaceInList old new (drop (length old) xs)
        else x :: replaceInList old new rest

-- Generate a function name from the einsum expression
export
generateFunctionName : String -> String
generateFunctionName einsumStr = 
  let withUnderscores = replaceString "->" "_" (replaceString "," "_" einsumStr)
  in "einsum_" ++ withUnderscores

-- Main function to generate Einsum function type from string
export
partial
generateEinsumType : String -> Elab ()
generateEinsumType einsumStr = do
  case parseEinsumString einsumStr of
    Left err => fail "Parse error in Einsum string: \{show err}"
    Right (MkEinsumExpr inputTy outputTy) => do
      let uniqueVars = toList (uniqueLabels inputTy)
      let functionName = generateFunctionName einsumStr
      let functionType = buildEinsumFunctionType uniqueVars inputTy (toList outputTy)
      
      -- Create the type declaration
      let claimData = MkIClaimData MW Public [] (MkTy EmptyFC (NoFC (UN (Basic functionName))) functionType)
      let tyDecl = IClaim (MkFCVal EmptyFC claimData)
      
      declare [tyDecl]
      
      -- Print confirmation
      logTerm "elab" 0 ("Generated function type: " ++ functionName) functionType


-- Generate some common Einsum function types
%runElab generateEinsumType "ij,jk->ik"    -- Matrix multiplication
%runElab generateEinsumType "ij->ji"       -- Transpose  
%runElab generateEinsumType "ij->"         -- Sum all elements
%runElab generateEinsumType "ij->i"        -- Sum over columns
%runElab generateEinsumType "ij->j"        -- Sum over rows
%runElab generateEinsumType "i,j->ij"      -- Outer product
%runElab generateEinsumType "ii->i"        -- Diagonal extraction
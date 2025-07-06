module Data.Tensor.Einsum.EinsumElab

import Data.DPair
import Data.List.Quantifiers
import Decidable.Equality
import Language.Reflection

import Data.Tensor.Einsum.EinsumExpr
import Misc

%language ElabReflection

------------------------------------------------------------
----- Elaborator Reflection for Einsum Function Generation
------------------------------------------------------------

||| Helper function to convert Char to variable name
charToVarName : Char -> Name
charToVarName c = UN (Basic (singleton c))

||| Generate [i, j, k] from ['i', 'j', 'k']
generateShapeVect : List Char -> TTImp
generateShapeVect [] = `([])
generateShapeVect (x :: xs) = 
  `(~(IVar EmptyFC (charToVarName x)) :: ~(generateShapeVect xs))

||| Generate Tensor' [i, j] a from shape ['i', 'j']
generateTensorType : List Char -> TTImp
generateTensorType shape = 
  let shapeVect = generateShapeVect shape
  in `(Tensor' ~(shapeVect) a)


generateOutputType : List Char -> TTImp
generateOutputType cs =
  let outputTensorType : TTImp := generateTensorType cs
      -- Add implicit {i, j, k : Nat} parameters
      withNatParams : TTImp := foldr (\var, acc => 
        IPi EmptyFC MW ImplicitArg (Just (charToVarName var)) `(Nat) acc) outputTensorType cs

      -- Add Num a constraint
      withNumConstraint : TTImp := IPi EmptyFC MW AutoImplicit Nothing `(Num a) withNatParams

      fullType : TTImp := IPi EmptyFC MW ImplicitArg (Just (UN (Basic "a"))) `(Type) withNumConstraint
  in fullType


listCharToType : List Char -> TTImp
listCharToType cs = %runElab check `(generateOutputType cs)
-- uniqueCharToShape : UniqueList Char -> List Nat
-- uniqueCharToShape x = ?uniqueCharToShape_rhs
-- 
-- einsumExprToOutputType : EinsumExpr Char -> Type -> Type
-- einsumExprToOutputType (MkEinsumExpr _ outputTy) a = Tensor' ?ss a


||| Build einsum function type with tensor shapes and implicit Nat parameters
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
    
    -- Add Num a constraint
    withNumConstraint : TTImp := IPi EmptyFC MW AutoImplicit Nothing `(Num a) withNatParams
    
    -- Add implicit {a : Type} parameter FIRST (before everything else)
    fullType : TTImp := IPi EmptyFC MW ImplicitArg (Just (UN (Basic "a"))) `(Type) withNumConstraint
    
  in fullType

||| Generate a function name from the einsum expression
public export
generateFunctionName : String -> String
generateFunctionName einsumStr = "einsum_" ++ withUnderscores where
  withUnderscores = replaceString "->" "__" (replaceString "," "_" einsumStr)


||| Main function to generate Einsum function type from string
export
partial
generateEinsumType : String -> Elab ()
generateEinsumType einsumStr = do
  case parseEinsumString einsumStr of
    Left err => fail "Parse error in Einsum string: \{show err}"
    Right (MkEinsumExpr inputTy outputTy) => do
      let uniqueVars = toList (uniqueJoin inputTy)
          fnName = generateFunctionName einsumStr
          fnType = buildEinsumFunctionType uniqueVars inputTy (toList outputTy)
      
          -- Create the type declaration
          claimData = MkIClaimData MW Public [] (MkTy EmptyFC (NoFC (UN (Basic fnName))) fnType)
          tyDecl = IClaim (MkFCVal EmptyFC claimData)
      
      declare [tyDecl]

-- Macro that provides NumPy-like einsum("ij,jk->ik", m, n) syntax  
-- This automatically generates einsum functions on-demand with dummy implementation
export
partial
einsum : {a : Type} -> {shapes : List Type} ->
  (exprStr : String) ->
  (args : HList shapes) ->
  Elab a
einsum exprStr args = do
  case parseEinsumString exprStr of
    Left err => fail "Parse error in Einsum string: \{show err}"
    Right expr@(MkEinsumExpr inputTy outputTy) => do
      let inpLength : Nat := length inputTy
      when (inpLength /= length shapes) $
        fail "Argument count mismatch: \{toString expr} defines \{show inpLength} inputs, but we got \{show (length shapes)} arguments"
      
      let uniqueVars = toList (uniqueJoin inputTy)
          fnName = generateFunctionName exprStr
          fnType = buildEinsumFunctionType uniqueVars inputTy (toList outputTy)
          
          -- Generate the function declaration
          claimData = MkIClaimData MW Public [] (MkTy EmptyFC (NoFC (UN (Basic fnName))) fnType)
          tyDecl = IClaim (MkFCVal EmptyFC claimData)
          
          -- Build lambda parameters for each input tensor
          paramNames = [UN (Basic ("x" ++ show i)) | i <- [0..length inputTy `minus` 1]]
          lambdaParams = zip paramNames inputTy
          
          -- Create the implementation body that matches the output tensor shape
          -- Generate the output shape as a vector literal from the output type
          outputShape = generateShapeVect (toList outputTy)
          -- Create zeros' with the correct output shape and generic type 'a'
          implBody = `(zeros' {shape = ~outputShape} {a = a})
          
          -- Build the full lambda expression
          fullImpl = foldr (\(paramName, shape), body => 
                           ILam EmptyFC MW ExplicitArg (Just paramName) (generateTensorType shape) body) 
                          implBody lambdaParams
          
          -- Create the definition using the correct IDef pattern
          clause = PatClause EmptyFC (IVar EmptyFC (UN (Basic fnName))) fullImpl
          funDef = IDef EmptyFC (UN (Basic fnName)) [clause]

      -- Declare both the type and the implementation
      declare [tyDecl, funDef]

      -- Now call the generated function directly with the actual arguments
      case args of
        [] => fail "No arguments provided"
        [x] => do
          fn <- check (IVar EmptyFC (UN (Basic fnName)))
          pure (fn x)
        [x, y] => do
          fn <- check (IVar EmptyFC (UN (Basic fnName)))
          pure (fn x y)
        [x, y, z] => do
          fn <- check (IVar EmptyFC (UN (Basic fnName)))
          pure (fn x y z)
        _ => fail "More than 3 arguments not yet supported"


m : Tensor' [2, 3] Double
m = fromArray' [[1, 2, 3], [4, 5, 6]]

n : Tensor' [3, 4] Double
n = fromArray' [[1, 2, 3, 4], [5, 6, 7, 8], [9, 10, 11, 12]]

-- partial
-- myEinsum : {a : Type} -> {shapes : List Type} ->
--   (exprStr : String) ->
--   (args : HList shapes) ->
--   a
-- myEinsum exprStr args = %runElab einsum exprStr args

-- Test the fixed einsum macro with a unique pattern
testNewPattern : Tensor' [3, 2] Double
testNewPattern = %runElab einsum "ij->ji" [m]


-- Helper function to find character position in nested list
findCharPosition : Char -> List (List Char) -> Maybe (Nat, Nat)
findCharPosition c [] = Nothing
findCharPosition c (xs :: xss) = 
  case findIndex (== c) xs of
    Just innerIdx => Just (0, finToNat innerIdx)
    Nothing => case findCharPosition c xss of
      Just (outerIdx, innerIdx) => Just (S outerIdx, innerIdx)
      Nothing => Nothing

-- Helper function to get dimension size from tensor at given position
getTensorDimSize : {shapes : List (List Nat)} -> 
  (tensorIdx : Nat) -> 
  (dimIdx : Nat) -> 
  HList (shapes <&> (\sh => Tensor' sh a)) -> 
  Maybe Nat
getTensorDimSize {shapes = []} _ _ [] = Nothing
getTensorDimSize {shapes = (sh :: shs)} Z dimIdx (t :: ts) = 
  case inBounds dimIdx sh of
    Yes prf => Just (index dimIdx sh)
    No _ => Nothing
getTensorDimSize {shapes = (sh :: shs)} (S k) dimIdx (t :: ts) = 
  getTensorDimSize k dimIdx ts

getSize : {shapes : List (List Nat)} ->
  (outputName : Char) ->
  (inputNames : List (List Char)) -> 
  (inputTensors : HList (shapes <&> (\sh => Tensor' sh a))) ->
  Maybe Nat
getSize outputName inputNames inputTensors = do
  (tensorIdx, dimIdx) <- findCharPosition outputName inputNames
  getTensorDimSize tensorIdx dimIdx inputTensors


-- Helper function to get size from a list of shapes
getSizeFromList : Char -> List (List Char) -> List (List Nat) -> Maybe Nat
getSizeFromList outputName inputNames shapes = do
  (tensorIdx, dimIdx) <- findCharPosition outputName inputNames
  case inBounds tensorIdx shapes of
    Yes prf => 
      let tensorShape = index tensorIdx shapes
      in case inBounds dimIdx tensorShape of
        Yes prf2 => Just (index dimIdx tensorShape)
        No _ => Nothing
    No _ => Nothing

einsumComputeOutputTypeHelper2 : {a : Type} -> Num a =>
  EinsumExpr Char ->
  List (sh ** Tensor' sh a) ->
  Type
einsumComputeOutputTypeHelper2 (MkEinsumExpr inputTy outputTy) args = 
  let outputChars : List Char = toList outputTy
      shapes : List (List Nat) = map (\(sh ** _) => sh) args
      -- Create a simple HList-like structure for getSize
      maybeNats : List (Maybe Nat) = map (\c => getSizeFromList c inputTy shapes) outputChars
      result : Maybe (List Nat) = sequence maybeNats
  in case result of
    Just listOfNats => Tensor' listOfNats a
    Nothing => Void

einsumComputeOutputType : {a : Type} -> Num a =>
  (exprStr : String) -> 
  (args : List (sh ** Tensor' sh a)) ->
  Type
einsumComputeOutputType {a} exprStr args = case parseEinsumString exprStr of
  Left err => Void
  Right expr => einsumComputeOutputTypeHelper2 expr args
  
  


einsumImplementation : {a : Type} -> Num a =>
  {is : List Nat} -> {m : Nat} -> {ls : List Nat} -> 
  {inputShs : List (List Nat)} ->
  {outputSh : List Nat} ->
  {auto prf : (fromList outputSh) `IsFrom` is} ->
  List1 (Exists (\sh => (Tensor' sh a, (fromList sh) `IsFrom` ls))) ->
  Tensor' outputSh a
einsumImplementation xs = ?hmma
--   -- According to the blog post, einsum works as nested for loops
--   -- 1. Initialize output tensor to zeros
--   let outputTensor : Tensor' outputSh a := zeros'
--   -- 2. For each combination of free indices (outer loops)
--   -- 3. For each combination of summation indices (inner loops)  
--   -- 4. Compute product of all input tensors at appropriate indices
--   -- 5. Add this product to output tensor at current free index position
--   in 
--   -- This is a simplified implementation that needs to be expanded
--   -- based on the actual index manipulation and tensor operations
--   -- The core idea is to iterate through all valid index combinations
--   -- and perform the sum of products as described in the blog post
--   case xs of
--     (x ::: xs) => 
--       -- For now, we return the zero tensor as a placeholder
--       -- The full implementation would need to:
--       -- 1. Extract the tensors from the existential types
--       -- 2. Create index iterators for free and summation indices  
--       -- 3. Implement the nested loops as described in the blog post
--       -- 4. Perform the products and sums according to Einstein notation
--       outputTensor


{-
TODO interesting cases of above:
a) one output index, repeated in input: M[i] += M[i, i] 
This means that the einsum string determines where to apply it.
Though, notably we've already *created the variables via Elab reflection*, so we should be able to apply them?
I.e. we should be able to 'find all occurences of i' in context, and apply the current value to it?

Consider
einsum "ii->i" m 
vs
einsum "ij->i" m

If we have a matrix m : Tensor' [3, 3] a

in both cases we'd need to look at the free index i, and then realise that depending on the einsum string we'd need to ..

In both we'd need to look at the free index i, and then realise that depending on the string we'd need to 

---

einsum "isj->ij" t



-}



batchedMatMul' : {a : Type} ->  Num a => {h, i, j, k : Nat} ->
  Tensor' [h, i, j] a -> Tensor' [h, j, k] a -> Tensor' [h, i, k] a
batchedMatMul' m n = %runElab einsum "bij,bjk->bik" [m, n]

matMul' : {a : Type} ->  Num a => {i, j, k : Nat} ->
  Tensor' [i, j] a -> Tensor' [j, k] a -> Tensor' [i, k] a
matMul' m n = %runElab einsum "ij,jk->ik" [m, n]

outer' : {a : Type} -> Num a => {i, j : Nat} ->
  Tensor' [i] a -> Tensor' [j] a -> Tensor' [i, j] a
outer' v w = %runElab einsum "i,j->ij" [v, w]

inner' : {a : Type} -> Num a => {i : Nat} ->
  Tensor' [i] a -> Tensor' [i] a -> Tensor' [] a
inner' v w = %runElab einsum "i,i->" [v, w]

trace' : {a : Type} -> Num a => {i : Nat} ->
  Tensor' [i, i] a -> Tensor' [] a
trace' m = %runElab einsum "ii->" [m]

diag' : {a : Type} -> Num a => {i : Nat} ->
  Tensor' [i, i] a -> Tensor' [i] a
diag' m = %runElab einsum "ii->i" [m]

sum' : {a : Type} -> Num a => {i : Nat} ->
  Tensor' [i] a -> Tensor' [] a
sum' v = %runElab einsum "i->" [v]
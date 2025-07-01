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


hListToTTImp : HList shapes -> Elab (List TTImp)
hListToTTImp [] = pure []
hListToTTImp (x :: xs) = do
  quotedX <- quote x
  quotedXs <- hListToTTImp xs
  pure (quotedX :: quotedXs)

-- Macro that provides NumPy-like einsum("ij,jk->ik", m, n) syntax  
-- This automatically generates einsum functions on-demand with dummy implementation
export
partial
einsum : {shapes : List Type} ->
  (exprStr : String) ->
  (args : HList shapes) ->
  Elab a
einsum exprStr args = do
  case parseEinsumString exprStr of
    Left err => fail "Parse error in Einsum string: \{show err}"
    Right expr@(MkEinsumExpr inputTy outputTy) => do
      when (length (inputTy) /= length shapes) $
        fail "Argument count mismatch: \{toString expr} defines \{show (length inputTy)} inputs, but we got \{show (length shapes)} arguments"
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

      
          -- Create the function call
          functionVar = IVar EmptyFC (UN (Basic fnName))
      ttimpArgs <- hListToTTImp args
      let functionCall = foldl (\acc, arg => IApp EmptyFC acc arg) functionVar ttimpArgs
      
      -- Declare both the type and the implementation (this is an Elab action)
      declare [tyDecl, funDef]
      
      -- Use check to convert TTImp to the expected tensor type
      check functionCall

m : Tensor' [2, 3] Double
m = fromArray' [[1, 2, 3], [4, 5, 6]]

n : Tensor' [3, 4] Double
n = fromArray' [[1, 2, 3, 4], [5, 6, 7, 8], [9, 10, 11, 12]]


-- listOfTensors : HList [Tensor' [2, 3] Double, Tensor' [3, 4] Double]
-- listOfTensors = [m, n]


-- Test the fixed einsum macro with a unique pattern
-- testNewPattern : Tensor' [2] Double
-- testNewPattern = %runElab einsum "ij,ij->i" [m, m]

einsumImplementation : {a : Type} -> Num a => {is : List Nat} -> {m : Nat} -> {ls : List Nat} -> 
  {inputShs : List (Exists (\n => Vect n Nat))} ->
  {outputSh : Vect m Nat} ->
  {auto prf : (fromVect outputSh) `IsFrom` is} ->
  List (Exists (\sh => (Tensor' sh a, (fromVect sh) `IsFrom` ls))) ->
  Tensor' outputSh a
einsumImplementation xs = 
  -- According to the blog post, einsum works as nested for loops
  -- 1. Initialize output tensor to zeros
  let outputTensor : Tensor' outputSh a := zeros'
  -- 2. For each combination of free indices (outer loops)
  -- 3. For each combination of summation indices (inner loops)  
  -- 4. Compute product of all input tensors at appropriate indices
  -- 5. Add this product to output tensor at current free index position
  in 
  -- This is a simplified implementation that needs to be expanded
  -- based on the actual index manipulation and tensor operations
  -- The core idea is to iterate through all valid index combinations
  -- and perform the sum of products as described in the blog post
  case xs of
    [] => outputTensor  -- No inputs, return zeros
    _ => 
      -- For now, we return the zero tensor as a placeholder
      -- The full implementation would need to:
      -- 1. Extract the tensors from the existential types
      -- 2. Create index iterators for free and summation indices  
      -- 3. Implement the nested loops as described in the blog post
      -- 4. Perform the products and sums according to Einstein notation
      outputTensor


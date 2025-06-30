module Data.Tensor.Einsum.EinsumElab

import Data.Tensor.Einsum.EinsumExpr
import Decidable.Equality
import Misc

import Language.Reflection

%language ElabReflection

----------------------------------------
----- Elaborator Reflection for Einsum Function Generation
----------------------------------------

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

||| Build function type with implicit Nat parameters and explicit tensor parameters
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
      let functionName = generateFunctionName einsumStr
      let functionType = buildEinsumFunctionType uniqueVars inputTy (toList outputTy)
      
      -- Create the type declaration
      let claimData = MkIClaimData MW Public [] (MkTy EmptyFC (NoFC (UN (Basic functionName))) functionType)
      let tyDecl = IClaim (MkFCVal EmptyFC claimData)
      
      declare [tyDecl]
      
      -- Print confirmation
      logTerm "elab" 0 ("Generated function type: " ++ functionName) functionType


-- Macro that provides NumPy-like einsum("ij,jk->ik", m, n) syntax  
-- This automatically generates einsum functions on-demand with dummy implementation
export
partial
einsum : String -> List TTImp -> Elab a
einsum exprStr args = case parseEinsumString exprStr of
  Left err => fail "Parse error in Einsum string: \{show err}"
  Right (MkEinsumExpr inputTy outputTy) => do
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
        functionCall = foldl (\acc, arg => IApp EmptyFC acc arg) functionVar args
    
    -- Declare both the type and the implementation (this is an Elab action)
    declare [tyDecl, funDef]
    
    -- Use check to convert TTImp to the expected tensor type
    check functionCall

m : Tensor' [2, 3] Double
m = fromArray' [[1, 2, 3], [4, 5, 6]]

n : Tensor' [3, 4] Double
n = fromArray' [[1, 2, 3, 4], [5, 6, 7, 8], [9, 10, 11, 12]]

-- Test the fixed einsum macro with a unique pattern
testNewPattern : Tensor' [2, 4] Double
testNewPattern = %runElab einsum "ij,jk->ik" [`(m), `(n)]
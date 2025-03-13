module Transformers

import Data.Vect

-- Matrix representation as a vector of vectors
data Matrix : (rows : Nat) -> (cols : Nat) -> Type -> Type where
  MkMatrix : Vect r (Vect c a) -> Matrix r c a

-- Show instance for Matrix
Show a => Show (Matrix r c a) where
  show (MkMatrix xs) = show xs

-- Functor instance for Matrix
Functor (Matrix r c) where
  map f (MkMatrix xs) = MkMatrix (map (map f) xs)

-- Extract the matrix data
getMatrix : Matrix r c a -> Vect r (Vect c a)
getMatrix (MkMatrix xs) = xs

-- Transposing vectors of vectors
transposeVectors : {r, c : Nat} -> Vect r (Vect c a) -> Vect c (Vect r a)
transposeVectors {r=Z} {c} [] = replicate c []
transposeVectors {r=S k} {c} (x :: xs) = 
  let xsTrans = transposeVectors {r=k} {c} xs
  in zipWith (::) x xsTrans

-- Matrix transpose 
transpose : {r, c : Nat} -> Matrix r c a -> Matrix c r a
transpose {r} {c} (MkMatrix xs) = MkMatrix (transposeVectors {r} {c} xs)

-- Dot product of two vectors
dotProduct : Num a => Vect n a -> Vect n a -> a
dotProduct xs ys = sum (zipWith (*) xs ys)

-- Standard matrix multiplication (for comparison)
matrixMult : {n, m, p : Nat} -> Num a => Matrix n m a -> Matrix m p a -> Matrix n p a
matrixMult {n} {m} {p} (MkMatrix rows1) (MkMatrix rows2) = 
  let cols2 = transposeVectors {r=m} {c=p} rows2
      result = map (\row => map (dotProduct row) cols2) rows1
  in MkMatrix result

-- Applicative style operations
-- Apply a matrix of functions to a matrix of values (similar to <*>)
applyMatrix : {r, c : Nat} -> Matrix r c (a -> b) -> Matrix r c a -> Matrix r c b
applyMatrix (MkMatrix fs) (MkMatrix xs) = MkMatrix (zipWith (zipWith ($)) fs xs)

-- Create a matrix filled with a single value (similar to pure)
pureMatrix : {r, c : Nat} -> a -> Matrix r c a
pureMatrix {r} {c} x = MkMatrix (replicate r (replicate c x))

-- Matrix multiplication using applicative-style approach
-- We break down the operation into functional components
matrixMultApp : {n, m, p : Nat} -> Num a => Matrix n m a -> Matrix m p a -> Matrix n p a
matrixMultApp {n} {m} {p} matA matB =
  let
      -- Get the raw data
      rowsA = getMatrix matA
      colsB = getMatrix (transpose matB)
      
      -- Convert each row to a function that computes dot product
      rowToFunc : Vect m a -> Vect m a -> a
      rowToFunc row = dotProduct row
      
      -- Create function to compute one row of the result matrix
      computeRow : Vect m a -> Vect p (Vect m a) -> Vect p a
      computeRow row cols = map (\col => rowToFunc row col) cols
      
      -- Compute the result matrix
      resultRows = map (\row => computeRow row colsB) rowsA
  in MkMatrix resultRows

-- Example usage:
-- Create a 2x3 matrix
exampleMatrix1 : Matrix 2 3 Integer
exampleMatrix1 = MkMatrix [[1, 2, 3], [4, 5, 6]]

-- Create a 3x2 matrix
exampleMatrix2 : Matrix 3 2 Integer
exampleMatrix2 = MkMatrix [[7, 8], [9, 10], [11, 12]]

-- Multiply matrices using standard method
resultMatrix : Matrix 2 2 Integer
resultMatrix = matrixMult exampleMatrix1 exampleMatrix2

-- Multiply matrices using applicative style
resultMatrixApp : Matrix 2 2 Integer
resultMatrixApp = matrixMultApp exampleMatrix1 exampleMatrix2

-- Both should produce:
-- MkMatrix [[58, 64], [139, 154]]

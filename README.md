# Type safe neural network architectures

This is an Idris 2 tensor framework which:
* Is type-safe (meaning indexing and contractions fail at compile time unless types match)
* Works for non-cubical tensors (including trees, and streams)
* Is made to be ergonomically usable (see the examples)

```idris
||| Analogous to np.range, except the range is specified in the type
t0 : Tensor' [7] Double
t0 = range 

||| We can construct Tensors directly
t1 : Tensor' [3, 4] Double
t1 = fromArray' [ [0, 1, 2, 3]
                , [4, 5, 6, 7]
                , [8, 9, 10, 11]]


```


TODO:
* Type-safe einsum
* Type-safe broadcasting, reshaping and stacking
* In-place operations
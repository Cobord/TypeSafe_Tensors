# Type safe neural network architectures

This provides a tensor framework which:
* Is type-safe (meaning indexing and contractions fail at compile time unless types match)
* Works for non-cubical tensors (including trees, and streams)
* Is made to be ergonomically usable (see the examples)

It is written in a lanugage with first-class types Idris2, and is based on the theory of containers, allowing an ergonomic way to 

Planned:
* Type-safe einsum
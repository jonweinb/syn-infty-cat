# Prelude

Aliases used by Lecture 1. Later lectures will add more shared helpers here.

```rzk
#lang rzk-1

#def product
  ( A B : U)
  : U
  := Σ (_ : A) , B

#def prod
  ( A B : U)
  : U
  := Σ (_ : A) , B

#def concat
  ( A : U)
  ( x y z : A)
  ( p : x = y)
  ( q : y = z)
  : x = z
  :=
  idJ(A , y
  , ( \ z' q' → (x = z'))
  , p
  , z
  , q)
```

# Synthetic Lecture 4: Discrete and Rezk types

```rzk
#lang rzk-1
```

We have introduced Segal types as those types admitting composition, i.e., types that are close to being $\infty$-categories. This is not quite true because their notion of \emph{isomorphism} might not be well behaved. We will fix this by introducing the \emph{Rezk-completeness condition} (see also Nima's Analytic Lecture 5).

Furthermore, we will introduce \emph{discrete types}, corresponding to those $\infty$-categories that are $\infty$-groupoids.


## §4.1. Discrete types

There is a comparison map from paths to homomorphisms, by path induction:

$$ \text{hom-eq}_A : \prod_{x,y:A} (x = y) \to \hom_A(x,y) $$

```rzk
#def hom-eq
  ( A : U)
  ( x y : A)
  ( p : x = y)
  : hom A x y
  := ind-path (A) (x) (\ y' p' → hom A x y') ((id-hom A x)) (y) (p)
```

We call a type **discrete** if this map is a family of equivalences:

$$\text{is-discrete}(A) :\equiv \prod_{x,y:A} \text{is-equiv}(\text{hom-eq}_A(x,y))$$

```
#def is-discrete
  ( A : U)
  : U
  :=
    (x : A)
    → (y : A)
    → is-equiv (x = y)
      (hom A x y)
      (hom-eq A x y)
```

One can show that any discrete type is actually a Segal type.

## §4.2. Isomorphisms

We know would like to obtain a well-behaved notion of isomorphism in our Segal types. This will be done similarly as to our notion of equivalence: an arrow is an isomorphism if it comes with a section and a retraction, up to homotopy.

```rzk
#def has-retraction-arrow
  ( A : U)
  ( is-segal-A : is-segal A)
  ( x y : A)
  ( f : hom A x y)
  ( g : hom A y x)
  : U
  := (comp-is-segal A is-segal-A x y x f g) =_{hom A x x} (id-hom A x)

#def Retraction-arrow
  ( A : U)
  ( is-segal-A : is-segal A)
  ( x y : A)
  ( f : hom A x y)
  : U
  := Σ (g : hom A y x) , (has-retraction-arrow A is-segal-A x y f g)

#def has-section-arrow
  ( A : U)
  ( is-segal-A : is-segal A)
  ( x y : A)
  ( f : hom A x y)
  ( h : hom A y x)
  : U
  := (comp-is-segal A is-segal-A y x y h f) =_{hom A y y} (id-hom A y)

#def Section-arrow
  ( A : U)
  ( is-segal-A : is-segal A)
  ( x y : A)
  ( f : hom A x y)
  : U
  := Σ (h : hom A y x) , (has-section-arrow A is-segal-A x y f h)

```

With this, we can define the type of witnesses that $f$ is an isomorphism:

$$ \text{is-iso-arrow}(f) :\equiv \left(\sum_{g:\hom_A(y,x)} g \circ f = \mathrm{id}_x\right) \times
\left(\sum_{h:\hom_A(y,x)} f \circ h = \mathrm{id}_y\right)
$$

We then get the type of isomorphisms in $A$ from $x$ to $y$ as:

$$ \mathrm{Iso}_A(x,y) :\equiv \sum_{f : \hom_A(x,y)} \text{is-iso-arrow}(f) $$

```rzk
#def is-iso-arrow
  ( A : U)
  ( is-segal-A : is-segal A)
  ( x y : A)
  ( f : hom A x y)
  : U
  :=
    product
    ( Retraction-arrow A is-segal-A x y f)
    ( Section-arrow A is-segal-A x y f)

#def Iso
  ( A : U)
  ( is-segal-A : is-segal A)
  ( x y : A)
  : U
  := Σ (f : hom A x y) , is-iso-arrow A is-segal-A x y f

```

Every identity is an isomorphism:

```rzk
#def is-iso-arrow-id-hom
  ( A : U)
  ( is-segal-A : is-segal A)
  ( x : A)
  : is-iso-arrow A is-segal-A x x (id-hom A x)
  :=
    ( ( id-hom A x , comp-id-is-segal A is-segal-A x x (id-hom A x))
    , ( id-hom A x , comp-id-is-segal A is-segal-A x x (id-hom A x)))

#def iso-id-arrow
  ( A : U)
  ( is-segal-A : is-segal A)
  : ( x : A) → Iso A is-segal-A x x
  := \ x → (id-hom A x , is-iso-arrow-id-hom A is-segal-A x)
```

Two important facts about isomorphisms in Segal types:

* A morphism $f$ in a Segal type is an isomorphism if and only if it has an inverse.
* Being an isomorphism is a proposition.

We can define a comparison map from homomorphisms to isomorphisms:

$$ \text{hom-iso}_A : \prod_{x,y:A} \mathrm{Iso}_A(x,y) \to \hom_A(x,y) $$

```rzk
#def hom-iso
  ( A : U)
  ( is-segal-A : is-segal A)
  ( x y : A)
  : Iso A is-segal-A x y → hom A x y
  := \ (f , _) → f
```

## §4.3. Rezk types

Similarly to $\mathrm{hom-eq}$, we can define a map $\mathrm{iso-eq}$ witnessing that every path gives rise to an isomorphism:

$$ \text{iso-eq}_A : \prod_{x,y:A} (x=_Ay) \to \mathrm{Iso}_A(x,y)$$

```rzk
#def is-iso-arrow-hom-eq
  ( A : U)
  ( is-segal-A : is-segal A)
  ( x y : A)
  : ( p : x = y)
  → is-iso-arrow A is-segal-A x y (hom-eq A x y p)
  :=
    ind-path A x
    ( \ y' p' → is-iso-arrow A is-segal-A x y' (hom-eq A x y' p'))
    ( is-iso-arrow-id-hom A is-segal-A x)
    ( y)

#def iso-eq
  ( A : U)
  ( is-segal-A : is-segal A)
  ( x y : A)
  : ( x = y) → Iso A is-segal-A x y
  := \ p → (hom-eq A x y p , is-iso-arrow-hom-eq A is-segal-A x y p)
```

We call a type **Rezk** if it is Segal and the above is a family of equivalences:

$$ \text{is-rezk}(A) :\equiv \text{is-segal}(A) \times \prod_{x,y:A} \text{is-equiv}\left( \text{iso-eq}_A(x,y) \right) $$

This recovers the **complete Segal spaces** from Nima's lecture.

```rzk
#def is-rezk
  ( A : U)
  : U
  :=
    Σ ( is-segal-A : is-segal A)
    , ( ( x : A)
      → ( y : A)
      → is-equiv (x = y) (Iso A is-segal-A x y) (iso-eq A is-segal-A x y))
```

Rezk types are Segal:

```rzk
#def is-segal-is-rezk
  ( A : U)
  ( is-rezk-A : is-rezk A)
  : is-segal A
  := (first (is-rezk-A))
```

Furthermore, one can show that a type is discrete if and only if it is Rezk and all its arrows are isomorphisms.

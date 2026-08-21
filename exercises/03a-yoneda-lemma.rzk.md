# Exercises: Associativity in Segal types

```rzk
#lang rzk-1
```

The aim of this problem set is to prove the Yoneda lemma for Segal types, characterizing natural transformations between representable functors.

The argument given here is very easily adapted to proving a more general result characterizing natural transformations from a representable functor to either a *covariant family* (in the case of a covariant representable) or a *contravariant family* (in the case of a contravariant representable). But to pursue the general case would require a detour to explain these notions, which we do not discuss here.

In fact, an interesting generalization of the Yoneda lemma came out of this synthetic approach to higher category theory. There is a principle of *arrow induction* which is analogous to *path induction*, aka the mapping out universal property of identity types. This gives a further generalization of the Yoneda lemma that we call the *dependent Yoneda lemma*. As it is also stated using covariant or contravariant families, we also do not pursue it here. See [RS17] or the sHoTT library for details.

This is a literate `rzk` file that compiles independently of the rest of this repository (by duplicating definitions found elsewhere here). Typecheck by running `rzk typecheck exercises/03a-yoneda-lemma.rzk.md --allow-holes` from the root of this repository.

## Homotopy type theory prerequisites

Our work will require the following definitions from the homotopy type theory library.

Product types are special cases of sigma types.

```rzk
#def product
  ( A B : U)
  : U
  := Σ (_ : A) , B
```

The elimination rule for identity types defines an operation called *path induction*:

```rzk
#def ind-path
  ( A : U)
  ( x : A)
  ( C : (y : A) → (x = y) → U)
  ( d : C x refl)
  ( y : A)
  ( p : x = y)
  : C y p
  := idJ(A , x , C , d , y , p)
```

Using path induction, we can define *reversal* and *concatenation* of paths, as well as the *application* of functions to paths.

```rzk
#def rev
  ( A : U)
  ( x : A)
  ( y : A)
  ( p : x = y)
  : y = x
  := ind-path A x (\ y' → \ p' → (y' = x)) refl y p

#def concat
  ( A : U)
  ( x y z : A)
  ( p : x = y)
  ( q : y = z)
  : x = z
  :=
  ind-path A y (\ z' q' → (x = z')) p z q

#def ap
  ( A B : U)
  ( x y : A)
  ( f : A → B)
  ( p : x = y)
  : f x = f y
  :=
  ind-path A x (\ y' p' → f x = f y') refl y p
```

We will also need to project from a path in a sigma type to a path between the first components of the pairs.

```rzk
#def first-path-Σ
  ( A : U)
  ( B : A → U)
  ( s t : Σ (a : A) , B a)
  ( e : s = t)
  : first s = first t
  :=
  ind-path
  ( Σ ( a : A) , B a) s
  ( \ t' e' → first s = first t') refl t e
```

We will use the definitions of *contractible* types.

```rzk
#def is-contr
  ( A : U)
  : U
  := Σ (c : A) , (x : A) → c = x
```

For expediency, we just use the built in `first` and `second` to extract the center of contraction and the contracting homotopy.

Finally, to state the Yoneda lemma, we will assert that a particular map between types is an *equivalence*.

```rzk
#def is-equiv
  ( A B : U)
  ( f : A → B)
  : U
  :=
  product
  ( Σ ( r : B → A)
    , ( a : A) → r (f a) = a)
  ( Σ ( s : B → A)
    , ( b : B) → f (s b) = b)
```

## Review of Segal types

In simplicial HoTT, we can define certain shapes:

```rzk
#def Δ¹
  : 2 → TOPE
  := \ t → TOP

#def Δ²
  : ( 2 × 2) → TOPE
  := \ (t , s) → s ≤ t
```

Recall that a type `A` in simplicial HoTT comes with hom types, whose elements are called *arrows*.

```rzk
#def hom
  ( A : U)
  ( x y : A)
  : U
  :=
  ( t : Δ¹)
  → A [ t ≡ 0₂ ↦ x , t ≡ 1₂ ↦ y ]
```

In particular, for any `x : A` there is an *identity arrow* defined as the constant function at `x`.

```rzk
#def id-hom (A : U) (x : A)
  : hom A x x
  := ?
```

The shape `Δ²` parametrizes commutative triangles in `A`. Given `x y z : A` and arrows `f : hom A x y`, `g : hom A y z`, and `h : hom A x z` they form a commutative triangle just when there is an element in the following type.

```rzk
#def hom2
  ( A : U)
  ( x y z : A)
  ( f : hom A x y)
  ( g : hom A y z)
  ( h : hom A x z)
  : U
  :=
  ( ( t₁ , t₂) : Δ²)
  → A [ t₂ ≡ 0₂ ↦ f t₁
      , t₁ ≡ 1₂ ↦ g t₂
      , t₂ ≡ t₁ ↦ h t₂]
```

As your first exercise, prove that for any `f : hom A x y`, we can form two commutative triangles where the diagonal edge is `f` and one of the spine edges is the identity on `x` or on `y`.

```rzk
#def id-comp-witness
  ( A : U)
  ( x y : A)
  ( f : hom A x y)
  : hom2 A x x y (id-hom A x) f f
  := ?

#def comp-id-witness
  ( A : U)
  ( x y : A)
  ( f : hom A x y)
  : hom2 A x y y f (id-hom A y) f
  := ?
```

A type `A` is a *Segal type* when every composable pair of arrows has a unique composite.

```rzk
#def is-segal
  ( A : U)
  : U
  :=
  ( x : A) → (y : A) → (z : A)
  → ( f : hom A x y) → (g : hom A y z)
  → is-contr (Σ (h : hom A x z) , (hom2 A x y z f g h))
```

In this case, we can define a binary composition function and  a witness to the commutativity of the triangle involving the binary composite.

```rzk
#def comp-is-segal
  ( A : U)
  ( is-segal-A : is-segal A)
  ( x y z : A)
  ( f : hom A x y)
  ( g : hom A y z)
  : hom A x z
  := first (first (is-segal-A x y z f g))

#def witness-comp-is-segal
  ( A : U)
  ( is-segal-A : is-segal A)
  ( x y z : A)
  ( f : hom A x y)
  ( g : hom A y z)
  : hom2 A x y z f g (comp-is-segal A is-segal-A x y z f g)
  := second (first (is-segal-A x y z f g))
```

Moreover, if there is any other commutative triangle `alpha : hom2 A x y z f g h` then the binary composite of `f` and `g` equals `h`.

```rzk
#def uniqueness-comp-is-segal
  ( A : U)
  ( is-segal-A : is-segal A)
  ( x y z : A)
  ( f : hom A x y)
  ( g : hom A y z)
  ( h : hom A x z)
  ( alpha : hom2 A x y z f g h)
  : ( comp-is-segal A is-segal-A x y z f g) = h
  :=
  first-path-Σ
  ( hom A x z)
  ( hom2 A x y z f g)
  ( comp-is-segal A is-segal-A x y z f g
    , witness-comp-is-segal A is-segal-A x y z f g)
  ( h , alpha)
  ( ( second (is-segal-A x y z f g))
      ( h , alpha))
```

Use this infrastructure to prove that in a Segal type, the composite of `f` with an identity is *equal to* `f`.

```rzk
#def id-comp-is-segal
  ( A : U)
  ( is-segal-A : is-segal A)
  ( x y : A)
  ( f : hom A x y)
  : ( comp-is-segal A is-segal-A x x y (id-hom A x) f) = f
  := ?

#def comp-id-is-segal
  ( A : U)
  ( is-segal-A : is-segal A)
  ( x y : A)
  ( f : hom A x y)
  : ( comp-is-segal A is-segal-A x y y f (id-hom A y)) = f
  := ?
```

## Representable functors and natural transformations

Fix a Segal type `A` and element `a : A`. We refer to the family of types `z : A ⊢ hom A z a` as the *contravariant family represented by* `a`. It is the family whose elements are arrows with arbitrary domain and with codomain `a`.

The Yoneda lemma concerns characterizes natural transformations between representable functors so fix a second element `b : A` and consider the contravariant family `z : A ⊢ hom A z b` represented by `b`. What is a natural transformation?

The *data* of a natural transformation is given by its *components*, which are encoded by a dependent function
`ϕ : (z : A) → hom A z a → hom A z b`.

The adjective *natural* in the name *natural transformation* refers to a property called naturality, which refers to a commutative square defined for any `f : hom A x y`. The components of the natural transformation at `x` and `y` define functions: `ϕ x : hom A x a → hom A x b` and `ϕ y : hom A y a → hom A y b`. Composition with `f` defines functions
`hom A y a → hom A x a` and `hom A y b → hom A x b`. Naturality asserts that the square that starts with `hom A y a` and ends with `hom A x b` by applying a component of `ϕ` or composing with `f` in either order commutes.

This commutativity condition can be expressed elementwise: for any `v : hom A y a`, we require that

`( comp-is-segal A is-segal-A x y b f (ϕ y v))
  = ( ϕ x (comp-is-segal A is-segal-A x y a f v))`

In fact this is not a separate requirement, but is provable! See the [original Yoneda repository](https://emilyriehl.github.io/yoneda/master/simplicial-hott/13-yoneda-geodesic.rzk/), the sHoTT library, or the [Yoneda game](https://rzk-lang.github.io/yoneda-game/) for full details. As this proof takes a while to develop, we will just assume this result here.

```rzk
#assume naturality-contravariant-fiberwise-representable-transformation :
  ( A : U)
  → ( is-segal-A : is-segal A)
  → ( a b x y : A)
  → ( f : hom A x y)
  → ( v : hom A y a)
  → ( ϕ : (z : A) → hom A z a → hom A z b)
  → ( comp-is-segal A is-segal-A x y b f (ϕ y v))
  = ( ϕ x (comp-is-segal A is-segal-A x y a f v))
```

In summary, the type of natural transformations between representable functors is just given by `(z : A) → hom A z a → hom A z b`. There is no naturality condition needed in the definition because it is provable!

## The Yoneda lemma

We can now state and prove the Yoneda lemma. Its statement involves a function that takes a natural transformation `ϕ : (z : A) → hom A z a → hom A z b` and returns an element of `hom A a b` defined by evaluating at the identity. Your first task is to define this function:

```rzk
#def contra-evid
  ( A : U)
  ( a b : A)
  : ( ( z : A) → hom A z a → hom A z b) → hom A a b
  := ?
```

The Yoneda lemma states that this function `contra-evid` is an equivalence. To prove this we start by defining a function in the other direction:

```rzk
#def contra-yon
  ( A : U)
  ( is-segal-A : is-segal A)
  ( a b : A)
  : hom A a b → ((z : A) → hom A z a → hom A z b)
  := ?
```

To prove that these maps are inverse equivalences, we need to show that the composites are homotopic to the identity. One retraction is straightforward:

```rzk
#def contra-evid-yon
  ( A : U)
  ( is-segal-A : is-segal A)
  ( a b : A)
  ( v : hom A a b)
  : contra-evid A a b ((contra-yon A is-segal-A a b) v) = v
  := ?
```

The other retraction requires more work. Here we want a homotopy that has the form of an equation
`contra-yon A is-segal-A a b (contra-evid A a b ϕ) = ϕ` for all `ϕ : (z : A) → hom A z a → hom A z b`. This is an equation between two natural transformations so we will start by proving that both of these define the same functions when applied to arguments `x : A` and `f : hom A x a`. Work out why this is true on paper before attempting to fill in the following hole.

```rzk
#def contra-yon-evid-twice-pointwise uses (naturality-contravariant-fiberwise-representable-transformation)
  ( A : U)
  ( is-segal-A : is-segal A)
  ( a b : A)
  ( ϕ : (z : A) → hom A z a → hom A z b)
  ( x : A)
  ( f : hom A x a)
  : ( ( contra-yon A is-segal-A a b)
        ( ( contra-evid A a b) ϕ)) x f = ϕ x f
  := ?
```

To use this to conclude that
`contra-yon A is-segal-A a b (contra-evid A a b ϕ) = ϕ` we have to apply something called *function extensionality*, which says that you can get an equality between functions from a homotopy.

```rzk
#def htpy-eq
  ( X : U)
  ( A : X → U)
  ( f g : (x : X) → A x)
  ( p : f = g)
  : ( x : X) → (f x = g x)
  :=
  ind-path
    ( ( x : X) → A x)
    ( f)
    ( \ g' p' → (x : X) → (f x = g' x))
    ( \ x → refl)
    ( g)
    ( p)

#def FunExt
  : U
  :=
  ( X : U)
  → ( A : X → U)
  → ( f : (x : X) → A x)
  → ( g : (x : X) → A x)
  → is-equiv (f = g)
    ( ( x : X) → f x = g x) (htpy-eq X A f g)

#assume funext : FunExt
```

This assumption provides us with the following function

```rzk
#def eq-htpy uses (funext)
  ( X : U)
  ( A : X → U)
  ( f g : (x : X) → A x)
  : ( ( x : X) → f x = g x) → (f = g)
  := first (first (funext X A f g))
```

which we use to get equalities between functions from homotopies. Use this to prove the following:

```rzk
#def contra-yon-evid-once-pointwise uses (funext naturality-contravariant-fiberwise-representable-transformation)
  ( A : U)
  ( is-segal-A : is-segal A)
  ( a b : A)
  ( ϕ : (z : A) → hom A z a → hom A z b)
  ( x : A)
  : ( ( contra-yon A is-segal-A a b)
        ( ( contra-evid A a b) ϕ)) x = ϕ x
  := ?
```

And then use this to prove the retraction we wanted all along

```rzk
#def contra-yon-evid uses (funext naturality-contravariant-fiberwise-representable-transformation)
  ( A : U)
  ( is-segal-A : is-segal A)
  ( a b : A)
  ( ϕ : (z : A) → hom A z a → hom A z b)
  : ( contra-yon A is-segal-A a b)
        ( ( contra-evid A a b) ϕ) = ϕ
  := ?
```

We have now reached the boss level! Assemble all of these ingredients into a proof of the Yoneda lemma:

```rzk
#def contra-yoneda-lemma uses (funext naturality-contravariant-fiberwise-representable-transformation)
  ( A : U)
  ( is-segal-A : is-segal A)
  ( a b : A)
  : is-equiv ((z : A) → hom A z a → hom A z b) (hom A a b) (contra-evid A a b)
  :=
    ( ( ?
      , ?)
    , ( ?
      , ?))
```

If you want a further challenge: *dualize* this development to state and prove the Yoneda lemma for covariant representable functor `z : A ⊢ hom A a z`.

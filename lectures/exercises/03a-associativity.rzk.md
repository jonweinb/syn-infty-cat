# Exercises: Associativity in Segal types

```rzk
#lang rzk-1
```

The aim of this problem set is to prove associativity of composition in Segal types by following the geometric argument of [RS17]. This depends on the notion of *Segal types* introduced in the simplicial HoTT lecture as well as their basic infrastructure including `comp-is-segal`, `witness-comp-is-segal`, and `uniqueness-comp-is-segal`. Remind yourself what those functions do before proceeding.

Typecheck this file (and the previous files containing those definitions) by running `rzk typecheck --allow-holes` from the root of this repository. The `rzk.yaml` file tells `rzk` to typecheck the lecture files first, followed by this file.

Our aim is to prove that if `A` is a Segal type with elements `w x y z : A` and arrows
` f : hom A w x` and `g : hom A x y` and `h : hom A y z` then `h ∘ (g ∘ f) = (h ∘ g) ∘ f`, where the composition is expressed with the `comp-is-segal` function. This involves some geometry!


## Squares as arrows in arrows

In simplicial sets, a square is built by gluing two triangles together along the diagonal. Thus if we have a map from a triangle `Δ²` into a type `A`, we can build a square `Δ¹×Δ¹ → A` by mapping each constituent triangle separately.

This is permitted by an operation called `recOR` on the shape layer of Rzk. There is a logical equivalence between the topes `TOP` and the tope `(t ≤ s) ∨  (s ≤ t)` over `(t, s) : 2 × 2`. So we can define a function `\ (t , s) → ?` out of the square by specifying the pieces `\ (t , s) → recOR ( t ≤ s ↦ ? , s ≤ t ↦ ?)` separately provided these specifications are compatible on the intersection `(t ≤ s) ∧ (s ≤ t)`.



```rzk
#def unfolding-square
  ( A : U)
  ( triangle : Δ² → A)
  : Δ¹×Δ¹ → A
  :=
  \ (t , s) →
  recOR
    ( t ≤ s ↦ triangle (s , t)
    , s ≤ t ↦ triangle (t , s))
```

Now apply this construction in the special case of a square that is witnessing the composition of two composable morphisms in a Segal type:

<svg style="float: right" viewBox="0 0 200 200" width="150" height="150">
  <path style="fill: rgb(256,128,0,0.5); stroke-cap: round;" d="M 52 40 L 160 40 L 160 148 Z"></path>
  <path style="fill: rgb(256,128,0,0.5); stroke-cap: round;" d="M 40 52 L 40 160 L 148 160 Z"></path>
  <polyline points="40,30 160,30" stroke="black" stroke-width="3" marker-end="url(#arrow)"></polyline>
  <polyline points="170,45 170,160" stroke="black" stroke-width="3" marker-end="url(#arrow)"></polyline>
  <polyline points="40,40 160,160" stroke="red" stroke-width="3" marker-end="url(#arrow-red)"></polyline>
  <polyline points="30,40 30,160" stroke="black" stroke-width="3" marker-end="url(#arrow)"></polyline>
  <polyline points="45,170 160,170" stroke="black" stroke-width="3" marker-end="url(#arrow)"></polyline>
  <text x="30" y="30">x</text>
  <text x="170" y="30">y</text>
  <text x="170" y="170">z</text>
  <text x="30" y="170">y</text>
  <text x="100" y="15">f</text>
  <text x="185" y="100">g</text>
  <text x="90" y="110" transform="rotate(45, 90, 110)" fill="red">comp-is-segal</text>
  <text x="100" y="190">g</text>
  <text x="15" y="100">f</text>
</svg>

```rzk
#def witness-square-comp-is-segal
  ( A : U)
  ( is-segal-A : is-segal A)
  ( x y z : A)
  ( f : hom A x y)
  ( g : hom A y z)
  : Δ¹×Δ¹ → A
  := ?
```

We will interpret these squares are arrows in the arrow type of a type `A`.

```rzk
#def arr
  ( A : U)
  : U
  := Δ¹ → A
```

We can interpret the `witness-square-comp-is-segal` as an arrow in the arrow type from `f` to `g`:

<svg style="float: right" viewBox="0 0 200 200" width="150" height="150">
  <polyline points="170,45 170,160" stroke="black" stroke-width="3" marker-end="url(#arrow)"></polyline>
  <polyline points="30,40 30,160" stroke="black" stroke-width="3" marker-end="url(#arrow)"></polyline>
  <polyline points="40,100 160,100" stroke="red" stroke-width="6" marker-end="url(#arrow-red)"></polyline>
  <text x="30" y="30">x</text>
  <text x="170" y="30">y</text>
  <text x="170" y="170">z</text>
  <text x="30" y="170">y</text>
  <text x="15" y="100">f</text>
  <text x="185" y="100">g</text>
</svg>

```rzk
#def arr-in-arr-is-segal
  ( A : U)
  ( is-segal-A : is-segal A)
  ( x y z : A)
  ( f : hom A x y)
  ( g : hom A y z)
  : hom (arr A) f g
  := ?
```

## Arrow types of Segal types are Segal types

Importantly the arrow type of a Segal type is a Segal type. We are just going to use this without supplying a proof but we should acknowledge that it uses an axiom called *extension extensionality* which characterizes identity types in extension types.

```rzk
#def ext-htpy-eq
  ( I : CUBE)
  ( ψ : I → TOPE)
  ( ϕ : ψ → TOPE)
  ( A : ψ → U)
  ( a : (t : ϕ) → A t)
  ( f g : (t : ψ) → A t [ϕ t ↦ a t])
  ( p : f = g)
  : ( t : ψ) → (f t =_{A t} g t) [ϕ t ↦ refl]
  :=
  ind-path
    ( ( t : ψ) → A t [ϕ t ↦ a t])
    ( f)
    ( \ g' p' → (t : ψ)
      → ( f t =_{A t} g' t) [ϕ t ↦ refl])
    ( \ _ → refl)
    ( g)
    ( p)

#def ExtExt
  : U
  :=
  ( ( I : CUBE)
  → ( ψ : I → TOPE)
  → ( ϕ : ψ → TOPE)
  → ( A : ψ → U)
  → ( a : (t : ϕ) → A t)
  → ( f : (t : ψ) → A t [ϕ t ↦ a t])
  → ( g : (t : ψ) → A t [ϕ t ↦ a t])
  → is-equiv
    ( f = g)
    ( ( t : ψ)
      → ( f t =_{A t} g t) [ϕ t ↦ refl])
    ( ext-htpy-eq I ψ ϕ A a f g))
```

To use this, we make an assumption:

```
#assume extext : ExtExt
```

except we are not doing this here to avoid an unused variable error when this file is compiled. The above is a code block but not an `rzk` code block, so it is not seen by the typechecker. The following theorem can proven using `extext`, but we just assume it here:

```rzk
#assume is-segal-arr :
  ( A : U) → (is-segal A) → is-segal (arr A)
```

## Associativity

Back to associativity! Assume now that `A` is a Segal type with elements `w x y z : A` and three composable arrows `f : hom A w x`, `g : hom A x y`, and `h : hom A y z`. Using the fact that `arr A` is a Segal type, we can compose the arrow from `f` to `g` defined by `arr-in-arr-is-segal` and an analogous arrow from `g` to `h`. We will actually use the witness to this composition rather than just the composite arrow from `f` to `h`:

<svg style="float: right" viewBox="0 0 200 250" width="150" height="200">
  <polyline points="170,45 170,160" stroke="black" stroke-width="3" marker-end="url(#arrow)"></polyline>
  <polyline points="30,40 30,160" stroke="black" stroke-width="3" marker-end="url(#arrow)"></polyline>
  <polyline points="40,100 160,100" stroke="red" stroke-width="6" marker-end="url(#arrow-red)"></polyline>
  <polyline points="40,30 160,30" stroke="lightgrey" stroke-width="3"></polyline>
  <polyline points="40,170 160,170" stroke="lightgrey" stroke-width="3"></polyline>
  <path style="fill: rgb(256,128,0,0.5); stroke-cap: round;" d="M 40 100 L 160 100 L 100 130 Z"></path>
  <polyline points="100,70 100,190" stroke="black" stroke-width="3" marker-end="url(#arrow)"></polyline>
  <polyline points="155,105 105,130" stroke="red" stroke-width="6" marker-end="url(#arrow-red)"></polyline>
  <polyline points="45,105 95,130" stroke="red" stroke-width="6" marker-end="url(#arrow-red)"></polyline>
  <polyline points="155,35 105,55" stroke="lightgrey" stroke-width="3"></polyline>
  <polyline points="45,35 95,55" stroke="lightgrey" stroke-width="3"></polyline>
  <polyline points="155,175 105,195" stroke="lightgrey" stroke-width="3"></polyline>
  <polyline points="45,175 95,195" stroke="lightgrey" stroke-width="3"></polyline>
  <text x="30" y="30">w</text>
  <text x="170" y="30">x</text>
  <text x="30" y="170">x</text>
  <text x="170" y="170">y</text>
  <text x="100" y="60">y</text>
  <text x="100" y="200">z</text>
  <text x="15" y="100">f</text>
  <text x="185" y="100">g</text>
  <text x="90" y="150">h</text>
</svg>

```rzk
#def witness-associative-is-segal uses (is-segal-arr)
  ( A : U)
  ( is-segal-A : is-segal A)
  ( w x y z : A)
  ( f : hom A w x)
  ( g : hom A x y)
  ( h : hom A y z)
  : hom2 (arr A) f g h
    ( arr-in-arr-is-segal A is-segal-A w x y f g)
    ( arr-in-arr-is-segal A is-segal-A x y z g h)
    ( comp-is-segal (arr A) (is-segal-arr A is-segal-A)
      ( f)
      ( g)
      ( h)
      ( arr-in-arr-is-segal A is-segal-A w x y f g)
      ( arr-in-arr-is-segal A is-segal-A x y z g h))
  := ?
```

This `witness-associative-is-segal` defines a map `Δ² → Δ¹ → A` which curries to define a map `Δ²×Δ¹ → A`. We will extract a tetrahedron `Δ³ → A` from this data whose spine is `f` followed by `g` followed by `h`. This is done via a particular map `Δ³ → Δ²×Δ¹` defined by `\ ((t, s), r) → ((t, r), s)`.

<svg style="float: right" viewBox="0 0 200 250" width="150" height="200">
  <path style="fill: rgb(256,128,0,0.5); stroke-cap: round;"
    d="M 35 35 L 165 35 L 165 165 L 102 190 Z"></path>
  <polyline points="170,45 170,160" stroke="black" stroke-width="3" marker-end="url(#arrow)"></polyline>
  <polyline points="30,40 95,190" stroke="red" stroke-width="3" marker-end="url(#arrow-red)"></polyline>
  <polyline points="40,40 160,160" stroke="red" stroke-width="3" marker-end="url(#arrow-red)"></polyline>
  <polyline points="160,40 110,180" stroke="red" stroke-width="3" marker-end="url(#arrow-red)"></polyline>
  <polyline points="40,30 160,30" stroke="black" stroke-width="3" marker-end="url(#arrow)"></polyline>
  <polyline points="155,175 110,195" stroke="black" stroke-width="3" marker-end="url(#arrow)"></polyline>
  <text x="30" y="30">w</text>
  <text x="170" y="30">x</text>
  <text x="170" y="170">y</text>
  <text x="100" y="200">z</text>
  <text x="185" y="100">g</text>
  <text x="100" y="15">f</text>
  <text x="140" y="205">h</text>
</svg>

```rzk
#def tetrahedron-associative-is-segal uses (is-segal-arr)
  ( A : U)
  ( is-segal-A : is-segal A)
  ( w x y z : A)
  ( f : hom A w x)
  ( g : hom A x y)
  ( h : hom A y z)
  : Δ³ → A
  :=
    \ ((t , s) , r) →
    ( witness-associative-is-segal A is-segal-A w x y z f g h) (t , r) s
```

Using this data, we can extract a diagonal edge, defining the triple composite arrow from `w` to `z`.

<svg style="float: right" viewBox="0 0 200 250" width="150" height="200">
  <path style="fill: rgb(128,128,128,0.5); stroke-cap: round;"
    d="M 35 35 L 165 35 L 165 165 L 102 190 Z"></path>
  <polyline points="170,45 170,160" stroke="black" stroke-width="3" marker-end="url(#arrow)"></polyline>
  <polyline points="30,40 95,190" stroke="red" stroke-width="3" marker-end="url(#arrow-red)"></polyline>
  <polyline points="40,40 160,160" stroke="grey" stroke-width="3" marker-end="url(#arrow-grey)"></polyline>
  <polyline points="160,40 110,180" stroke="grey" stroke-width="3" marker-end="url(#arrow-grey)"></polyline>
  <polyline points="40,30 160,30" stroke="black" stroke-width="3" marker-end="url(#arrow)"></polyline>
  <polyline points="155,175 110,195" stroke="black" stroke-width="3" marker-end="url(#arrow)"></polyline>
  <text x="30" y="30">w</text>
  <text x="170" y="30">x</text>
  <text x="170" y="170">y</text>
  <text x="100" y="200">z</text>
  <text x="185" y="100">g</text>
  <text x="100" y="15">f</text>
  <text x="140" y="205">h</text>
</svg>

```rzk
#def triple-comp-is-segal uses (is-segal-arr)
  ( A : U)
  ( is-segal-A : is-segal A)
  ( w x y z : A)
  ( f : hom A w x)
  ( g : hom A x y)
  ( h : hom A y z)
  : hom A w z
  := ?
```

We also have witnesses that this triple composite arrow is a binary composite of both `g f` followed by `h` and `f` followed by `h g`.

<svg style="float: right" viewBox="0 0 200 250" width="150" height="200">
  <path style="fill: rgb(128,128,128,0.5); stroke-cap: round;"
    d="M 40 35 L 165 35 L 165 160 Z"></path>
  <path style="fill: rgb(256,128,0,0.5); stroke-cap: round;"
    d="M 35 40 L 160 165 L 102 190 Z"></path>
  <polyline points="170,45 170,160" stroke="black" stroke-width="3" marker-end="url(#arrow)"></polyline>
  <polyline points="30,40 95,190" stroke="red" stroke-width="3" marker-end="url(#arrow-red)"></polyline>
  <polyline points="40,40 160,160" stroke="red" stroke-width="3" marker-end="url(#arrow-red)"></polyline>
  <polyline points="160,40 110,180" stroke="grey" stroke-width="3" marker-end="url(#arrow-grey)"></polyline>
  <polyline points="40,30 160,30" stroke="black" stroke-width="3" marker-end="url(#arrow)"></polyline>
  <polyline points="155,175 110,195" stroke="black" stroke-width="3" marker-end="url(#arrow)"></polyline>
  <text x="30" y="30">w</text>
  <text x="170" y="30">x</text>
  <text x="170" y="170">y</text>
  <text x="100" y="200">z</text>
  <text x="185" y="100">g</text>
  <text x="100" y="15">f</text>
  <text x="140" y="205">h</text>
</svg>

```rzk
#def left-witness-associative-is-segal uses (is-segal-arr)
  ( A : U)
  ( is-segal-A : is-segal A)
  ( w x y z : A)
  ( f : hom A w x)
  ( g : hom A x y)
  ( h : hom A y z)
  : hom2 A w y z
    ( comp-is-segal A is-segal-A w x y f g)
    h
    ( triple-comp-is-segal A is-segal-A w x y z f g h)
  := ?
```

<svg style="float: right" viewBox="0 0 200 250" width="150" height="200">
  <path style="fill: rgb(256,128,0,0.5); stroke-cap: round;"
    d="M 35 35 L 155 35 L 100 185 Z"></path>
  <path style="fill: rgb(128,128,128,0.5); stroke-cap: round;"
    d="M 165 40 L 165 165 L 115 185 Z"></path>
  <polyline points="170,45 170,160" stroke="black" stroke-width="3" marker-end="url(#arrow)"></polyline>
  <polyline points="30,40 95,190" stroke="red" stroke-width="3" marker-end="url(#arrow-red)"></polyline>
  <polyline points="40,40 160,160" stroke="grey" stroke-width="3" marker-end="url(#arrow-grey)"></polyline>
  <polyline points="160,40 110,180" stroke="red" stroke-width="3" marker-end="url(#arrow-red)"></polyline>
  <polyline points="40,30 160,30" stroke="black" stroke-width="3" marker-end="url(#arrow)"></polyline>
  <polyline points="155,175 110,195" stroke="black" stroke-width="3" marker-end="url(#arrow)"></polyline>
  <text x="30" y="30">w</text>
  <text x="170" y="30">x</text>
  <text x="170" y="170">y</text>
  <text x="100" y="200">z</text>
  <text x="185" y="100">g</text>
  <text x="100" y="15">f</text>
  <text x="140" y="205">h</text>
</svg>

```rzk
#def right-witness-associative-is-segal uses (is-segal-arr)
  ( A : U)
  ( is-segal-A : is-segal A)
  ( w x y z : A)
  ( f : hom A w x)
  ( g : hom A x y)
  ( h : hom A y z)
  : hom2 A w x z
    ( f)
    ( comp-is-segal A is-segal-A x y z g h)
    ( triple-comp-is-segal A is-segal-A w x y z f g h)
  := ?
```

These witnesses are really commutative triangles with specified boundary. What we want to conclude is that the triple composite is *equal* to the composites of these composites, using identity types. This follows from the uniqueness of composition in the Segal type `A`.

```rzk
#def left-associative-is-segal uses (is-segal-arr)
  ( A : U)
  ( is-segal-A : is-segal A)
  ( w x y z : A)
  ( f : hom A w x)
  ( g : hom A x y)
  ( h : hom A y z)
  : ( comp-is-segal A is-segal-A w y z (comp-is-segal A is-segal-A w x y f g) h)
  = ( triple-comp-is-segal A is-segal-A w x y z f g h)
  := ?

#def right-associative-is-segal uses (is-segal-arr)
  ( A : U)
  ( is-segal-A : is-segal A)
  ( w x y z : A)
  ( f : hom A w x)
  ( g : hom A x y)
  ( h : hom A y z)
  : ( comp-is-segal A is-segal-A w x z f (comp-is-segal A is-segal-A x y z g h))
  = ( triple-comp-is-segal A is-segal-A w x y z f g h)
  := ?
```

Using this we can finally prove associativity!

```rzk
#def associative-is-segal uses (is-segal-arr)
  ( A : U)
  ( is-segal-A : is-segal A)
  ( w x y z : A)
  ( f : hom A w x)
  ( g : hom A x y)
  ( h : hom A y z)
  : ( comp-is-segal A is-segal-A w y z (comp-is-segal A is-segal-A w x y f g) h)
  = ( comp-is-segal A is-segal-A w x z f (comp-is-segal A is-segal-A x y z g h))
  := ?

#def rev-associative-is-segal uses (is-segal-arr)
  ( A : U)
  ( is-segal-A : is-segal A)
  ( w x y z : A)
  ( f : hom A w x)
  ( g : hom A x y)
  ( h : hom A y z)
  : ( comp-is-segal A is-segal-A w x z f (comp-is-segal A is-segal-A x y z g h))
  = ( comp-is-segal A is-segal-A w y z (comp-is-segal A is-segal-A w x y f g) h)
  := ?
```

# Synthetic Lecture 1: Introduction to homotopy type theory

[ICERM Teaching Higher Category Theory with Computers, Aug 17 - 21, 2026](https://icerm.brown.edu/program/topical_workshop/tw-26-thc)

This lecture series is a hands-on introduction to higher category theory in the proof assistant [Rzk](https://rzk-lang.github.io/). We will work **synthetically**, i.e., in a language where the underlying homotopical notions will be primitives. Our language will be based on **homotopy type theory**, namely an extension thereof that adds simplicial shapes to reason about $\infty$-categories. The notation of the lectures will (largely) be in line with the architecture of the [sHoTT library](https://rzk-lang.github.io/sHoTT/) and its [code conventions](https://rzk-lang.github.io/sHoTT/STYLEGUIDE/).

We will do [literate programming](https://en.wikipedia.org/wiki/Literate_programming) in `.rzk.md`-files. Since Rzk supports various languages, at the beginning of each file, we have to explicitly set the language mode of Rzk:
```rzk

#lang rzk-1

```

To typecheck the code in the lecture notes do the following:

1. Clone the repository locally (e.g. through `gh repo clone jonweinb/syn-infty-cat`)
2. On a terminal, `cd` into the downloaded repository.
3. On the terminal run:
`rzk typecheck --allow-holes lectures/*.rzk.md`


Today's lecture is an introduction to (homotopy) type theory in Rzk. We will introduce:
* dependent types
* how to construct new types out of old ones using type formers
* identity types
* basic synthetic homotopy theory in type theory

## §1.1. Dependent types

Type theory has three basic notions:

1. **terms** or **elements** $a,b,c \ldots$
2. **types** $A, B, C \ldots$
3. **contexts** $\Gamma, \Delta, \Xi \ldots$

Each term belongs to one and only one type. We write

$$a : A$$

to mean that "a is a term of type A."

This is roughly analogous to an element $a$ being contained in a set $A$: $a \in A$. But we will see soon that there are important differences between sets and types.

If $A$ is a type, a **dependent type** $B$ over $A$ consists of a collection of types $B(a)$ for all $a:A$.

This dependency can be iterated. For instance, for all $a:A$ and $b:B(a)$ we might have a types $C(a,b)$.

This is also written as:

$$a:A, b:B(a) \vdash C(a,b)$$

For example, assuming a type $\mathbb N$ of natural numbers, we might want to capture the dependent type of $n$-dimensional standard Euclidean vector space $\mathbb R^n$:

$$ n : \mathbb N \vdash \mathbb R^n $$

The list of declarations on the left hand side of the turnstile is called a **context**. In general, a context $\Gamma$ is a finite ordered list of (hypothetical) term declarations:

$$\Gamma \equiv [a_1 : A_1, a_2 : A_2(a_1), a_3 : A_3(a_1,a_2), a_n : A_n(a_1, \ldots, a_{n-1})]$$

A general **typing judgment** has the form

$$\Gamma \vdash A ~~\text{type}$$

or, for short:

$$\Gamma \vdash A$$

We say that *"A is a type in context $\Gamma$."*

Just as types can be depend on contexts, so can terms:

$$a :A, b : B(a) \vdash c(a,b) : C(a,b)$$

In general, we write:

$$\Gamma \vdash a:A$$

For intuition, remember how you would start a mathematical definition or proof with a clause like "Let $n$ be a natural number" or similar. You can think of the context $\Gamma$ as the declarations after the "let...".

In the above example, $n : \mathbb N \vdash \mathbb R^n$ we can capture the family of zero vectors as

$$ n : \mathbb N \vdash \mathbf{0}_n :  \mathbb R^n. $$


If $A$ is a type with no dependency, we say then $A$ is a type in the **empty context**:

$${}\vdash A \quad\text{or}\quad \cdot\vdash A$$

E.g., the type naturals itself does not depend on any other type, so

$$ \vdash \mathbb N.$$


## §1.2. Hello Rzk!

Rzk implements dependent type theory. We want to start by formalizing the following simple fact:

*"If A is a type and a:A, then there is a term of type A."*

The judgment that $A$ be a type in Rzk is encoded by expressing that $A$ itself is a term of the **universe type** $\mathcal U$, the type of all types.

If this makes you nervous then you are right: just as in set theory we run into paradoxes when trying to naively assert a "set of all sets" analogous problems happen when assuming a "type of all types." The typical solution is to restrict the sizes: small sets form a large universe, large sets form a very large universe etc.

We will not bother with this and just work relative to a single fixed universe $\mathcal U$ called `U` in Rzk.

**Beware:** Rzk validates the paradoxical statement `U:U` (also called "type-in-type") which strictly speaking makes it inconsistent. We expect you won't use this property in this course anyway. :-)

Thus, the assertion that $A$ be a type is written in Rzk as `A : U`.

Let us come back to our first statement:

*"If A is a type and a:A, then there is a term of type A."*

Our **assumptions** are written in parentheses and left of the colon:

*"If A is a type and a is a term of type A..."*

Our **goal** is the unique type on the right of the colon:

*"...then there is a term of type A"*

The question mark ``?`` represents an unfulfilled goal, also called a **hole**. We can fill the hole by replacing it by a term of the appropriate type.

In this case, since we already know that $a:A$, we can just use this same term to fill the hole:

```rzk
#def simple
  ( A : U)
  ( a : A)
  : A
  := a
```

This essentially corresponds to defining the **identity function** of the type $A$.

In fact, treating functions themselves as values is a key paradigm of type theory and functional programming.

## §1.3: Dependent function types

If $A$ and $B$ are types, we can form the **function type** $A \to B$. Its terms $f : A \to B$ should behave exactly as we know from functions: for every term $a:A$ there should be a unique term $b : B$, i.e.:

$$a:A \vdash f(a) : B$$

To reify such an assignment into a single term we write it as:

$$\lambda a . f(a) : A \to B$$

In mathematics, we would write something akin to:

$$A \to B, \, a \mapsto f(a)$$

We call a term of the form $\lambda a.b$ a **$\lambda$-abstraction**. In Rzk, instead of $\lambda a.b$ we write ``\ a -> b ``.

The identity function $\mathrm{id}_A : A \to A$ sends each $a : A$ to itself:

```rzk
#def id
  ( A : U)
  : A → A
  := \ a -> a
```

  We can also define a constant function: given types $A$ and $B$ and a term $x :B$, the **constant function** with value $x$ is defined as $\mathrm{const}_x :\equiv \lambda a.x : A \to B$:

```rzk

#def const
  ( A B : U)
  ( x : B)
  : A → B
  := \ _ -> x
```

  The $\lambda$-operator **build** terms of a function type: if for every $a : A$ we have a term $f(a) : B$ this defines a term $f:A \to B$.

Conversely, can we also **destroy** function terms? E.g., given a function $f : A \to B$ can we get a type of one of the original terms? Indeed, assuming we also have $a : A$ we get back a term in $B$ just by applying $f$ to $a$, denoted by $f(a) : B$.

In Rzk, this reads as follows:

```rzk
#def apply
    ( A B : U)
    ( f : A → B)
    ( a : A)
  : B
  := (f a)
```

Let us try to use this to define the composite of two functions: given types $A, B, C$ and functions $f : A \to B$ and $g : B \to C$ we want to express the **composite function** $g \circ f : A \to C$. Can you do it in Rzk using ``\ ``?

```rzk
#def compose
    ( A B C : U)
    ( g : B → C) (f : A → B)
  : A → C
  := \ a -> (g (f a))

```

What have we done so far? We have given some definitions and let Rzk check that the typing is correct---and this is basically all we will be doing! We will see soon how we can encode proofs in that way.

The $\to$-operator assigning to two types $A$ and $B$ a new type $A \to B$ is an example of a **type former**, constructing a new type out of old ones.

The contrast between building terms and destorying terms in type theory is analogous to constructors and destructors in programming.

Type-theoretic reasoning is often presented in a  **deductive systems** using derivations often denoted in the format:

$$ \frac{\text{Hypotheses}}{\text{Conclusion}}$$

This is not the notation in Rzk but it is standard in the literature, and it's convenient to introduce new type formers.

The behavior of type formers such as $\to$ is specified using the following kinds of rules:

1. **Formation rules:** When can I form the new type?

$$ \frac{\vdash A \quad \vdash B}{\vdash A \to B}(\text{$\to$-form})$$

2. **Introduction rules:** How can I construct terms of the new type?

$$ \frac{\vdash A \quad \vdash B \quad x : A \vdash f(x) : B}{\vdash \lambda x . f(x) : A \to B}(\text{$\to$-intro})$$

3. **Elimination rules:** How can I use the terms of the new type to construct terms of other types?

$$ \frac{\vdash A \quad \vdash B \quad \vdash f : A \to B \quad \vdash a:A}{\vdash f(a) : B}(\text{$\to$-elim})$$

So far, introduction for $\to$-types corresponds to the familiar process of defining a function through **abstracting** over a variable. Elimination is **applying** the function to a term in the domain. How do we ensure that these processes really behave in the way we expect?

This is done through an additional set of rules, called **computation rules**.

4. **Computation rules:**

4.1 **$\beta$-reduction rule:**

For a term $b$ let $b[a/x]$ denote the result obtained by syntactically replacing all occurrences in $b$ of $x$ by $a$. This operation is called **substitution**.

Now, consider a function presented by a $\lambda$-term $\lambda x.f$. Intuitively, evaluating this term at $a$ should yield exactly the function body $f$, with every occurrence of $x$ substituted by $a$. This is known from mathematics:

Consider the cube function $x \mapsto x^3$. Then

$$ (x \mapsto x^3)(2) = 2^3 $$

or in $\lambda$-notation:

$$ (\lambda x.x^3)(2) = 2^3 $$

 This does not automatically hold in type theory, and hence has to be postulated. This is called the **$\beta$-rule** (leaving the premises over the types and terms involved implicit):

$$ (\lambda x.f)(a) \equiv f[a/x] \qquad (\text{$\to$-$\beta$})$$



4.2 **$\eta$-conversion rule:** In type theory, a function should *name itself*. We want to refer to a function $\lambda x.f$ simply by $f$. This is achieved by the $\eta$-rule (again suppressing the implied premises):

$$ \lambda x.f(x) \equiv f \qquad(\text{$\to$-$\eta$}) $$

**Derivation trees** are built using the rules of the system.

To produce a tree that is valid in the system we have to ensure that the leaves are all **axioms** of our theory, meaning they have no premises. So far, we have no axioms, so all of our derivations are hypothetical: assuming the existence of some old types we can construct new types. We have yet to encounter axiomatic rules giving us the existence of some **base types** as primitives.

Nonetheless, we can make hypothetical derivations such as the following, corresponding to our definition of function composition:

$$
\dfrac
  {
    \vdash B
    \quad
    \vdash C
    \quad
    \vdash g : B \to C
    \quad
    \dfrac{\vdash A \quad \vdash B \quad \vdash f : A \to B \quad \vdash a : A}
      {\vdash f(a) : B}
  }
  {\vdash g(f(a)) : C}
$$

It is instructive to compare the tree-shaped derivation of function composition with our earlier Rzk counterpart. In this lecture series, we will mostly disregard the deductive system perspective and just focus on formalization. But we will present new type formers using rules, so it is useful to keep this perspective in the back of your mind as well.

A key idea of *dependent* type theory is that it should capture dependent or indexed constructions natively. Functions are ubiquitous in mathematics but they are sometimes not convenient. For instance, in differential geometry a vector field is defined as follows.

Let $M$ be a (topological/differentiable/smooth...) manifold and $p : TM \to M$ its tangent projection. A vector field on $M$ is a (continuous/differentiable/smooth...function) $X : M \to TM$ such that $p \circ X = \mathrm{id}_M$. This amounts to viewing $X$ as a generalized "function"

$$ p \mapsto X(p) \in T_p M $$

where $T_p M$ denotes the tangent space at the point $p \in M$.

Crucially, $X$ naturally appears here as a "function with varying codomain." To make this precise in set theory we need an additional condition, but in dependent type theory this will be a primitive operation on types, giving rise to **dependent function type** (also called **dependent product** or **$\prod$-type**):

Just as an ordinary function type captures ordinary functions $A \to B$, a dependent function type should capture **dependent functions** $(x : A ) \to B(x)$.

To make this rigoros, let $A$ be a type and $x : A \vdash B(x)$ be a dependent type. Then the **dependent function type** $(x:A) \to B(x)$ or $\prod_{x:A} B(x)$ is defined by the following rules:

1. **Formation rules:**

$$ \frac{\vdash A \quad x : A\vdash B(x)}{\vdash \prod_{x:A}B(x)}(\text{$\prod$-form})$$

2. **Introduction rules:**

$$ \frac{\vdash A \quad x : A\vdash B(x) \quad x : A \vdash f(x) : B(x)}{\vdash \lambda x . f(x) :\prod_{x:A}B(x)}(\text{$\prod$-intro})$$

3. **Elimination rules:**

$$ \frac{\vdash A \quad x:A\vdash B(x) \quad \vdash f : \prod_{x:A}B(x) \quad \vdash a:A}{\vdash f(a) : B(a) }(\text{$\prod$-elim}) $$

The $\beta$- and $\eta$-rules hold verbatim.

Recall the example from differential geometry. A vector field $X$ on a manifold $M$ can be understood as a **section** of the tangent bundle $p:TM \to M$.

More generally, given a (topological/fiber/vector...) bundle $p : E \to B$, we are interested in its sections, i.e., maps $\sigma : B \to E$ such that $p \circ \sigma = \mathrm{id}_B$. The latter conditions means exactly that $\sigma$ behaves like a dependent function

$$ (b \in B) \mapsto (\sigma(b) \in E_b) $$

where $E_b$ is the **fiber** $p^{-1}(b)$.

Analogously, in type theory, we also call a dependent function $f : \prod_{x:A} B(x)$ a **section** of $B$.

In particular, the bundle $p : E \to B$ gives rise (in a suitable sense) to a family of fibers $(E_b)_{b\in B}$.

We can do something similar in type theory as well: a dependent type $x :A \vdash B(x)$ is essentially the same as a function $B : A \to \mathcal U$, assigning to each $x:A$ the type $B(x)$.

In fact, this is how Rzk encodes dependent types in the first place: a dependent type $x :A \vdash B(x)$ corresponds to a function `B : A → U`.

With this at hand, we can now code up the $\prod$-elimination rule:

$$ \frac{\vdash A \quad x:A\vdash B(x) \quad \vdash f : \prod_{x:A}B(x) \quad \vdash a:A}{\vdash f(a) : B }(\text{$\prod$-elim}) $$

```rzk
#def dapply
    ( A : U)
    ( B : A → U)
    ( f : (x : A) → B x)
    ( a : A)
  : B a
  := f(a)
```


**Local vs. global style rules:** In dependent type theory, any rule can be used in any context. For notational simplicity we are hence presenting all our rules in **local** style, leaving an arbitrary background context $\Gamma$ implicit. For instance, the by $\prod$-formation rule

$$ \frac{\vdash A \quad x : A\vdash B(x)}{\vdash \prod_{x:A}B(x)}$$

is really short for

$$ \frac{\Gamma \vdash A \quad \Gamma, x : A\vdash B(x)}{\Gamma \vdash \prod_{x:A}B(x)}$$

where $\Gamma$ is an arbitrary context, i.e., a finite list of declarations

$$\Gamma \equiv [x_1 : A_1, x_2 : A_2(x_1), \ldots, x_n : A_n(x_1,\ldots, x_{n-1})].$$

For $\Gamma, x : A$ the notation $\Gamma,x:A$ stands for the **extended context**

$$\Gamma, x:A \equiv [x_1 : A_1, x_2 : A_2(x_1), \ldots, x_n : A_n(x_1,\ldots, x_{n-1}), x:A(x_1,\ldots,x_n)].$$

Sometimes, an extended context $\Gamma, x:A$ is also written as $\Gamma.A$.



## §1.4. Dependent pair types

Given types $A$ and $B$ we learned how to build the function type $A \to B$ (or its dependent analogue $\prod_{x:A} B(x)$). We'd like to build more interesting types out of given types.

An important construction in set theory is the **cartesian product** $A \times B$ of two sets whose elements are **ordered pairs** $(a,b)$, for instance encoded as Kuratowski pairs $\{\{a\}, \{a,b\}\}$.

In type theory, the cartesian product is introduced as follows as the **product type** or **pair type**:

1. **Formation rules:**

$$ \frac{\vdash A \quad \vdash B}{\vdash A \times B}(\text{$\times$-form})$$

2. **Introduction rules:**

$$ \frac{\vdash a:A \quad \vdash b:B}{\vdash (a,b) :A \times B}(\text{$\times$-intro})$$

3. **Elimination rules:**

$$\frac{\vdash p : A \times B}{\vdash \mathrm{first}(p) : A }(\text{$\times$-elim${}_1$})$$



$$\frac{\vdash p : A \times B}{\vdash \mathrm{second}(p) : A }(\text{$\times$-elim${}_2$})
$$

4. **Computation rules**

4.1 **$\beta$-reduction rules:**

$$\mathrm{first}(a,b) \equiv a \quad (\text{$\times$-$\beta_1$}), \qquad \mathrm{second}(a,b) \equiv b \quad (\text{$\times$-$\beta_2$})$$

4.2 **$\eta$-conversion rules:**

$$(\mathrm{first}(p), \mathrm{second}(p)) \equiv p  \quad (\text{$\times$-$\eta$})$$

In Rzk, we write `product A B` for $A \times B$.

Introduction is implemented using the parenthesis primitive `( , )`:

```rzk
#def pair
    ( A B : U)
    ( a : A)
    ( b : B)
  : prod A B
  := ?
```

Elimination is implemented using the primitives `first` and `second`:

```rzk
#def fst (A B : U) (p : prod A B)
  : A
  := ?

#def snd (A B : U) (p : prod A B)
  : B
  := ?
```

Coming back to the intuition from differential geometry,  think about how we drew an analogy between sections and dependent functions. In this view, we also see a connection between dependent types $b : B \vdash E(b)$ and bundles. In a bundle $p : E \to B$, the total space $E$ appears as the union of its fibers, $E \cong \coprod_{b \in B} p^{-1}(b)$. For instance, in the case of the tangent bundle $p : TM \to M$, we have $TM \cong \coprod_{p \in M} T_p M$, where $T_p M$ are the tangent vectors of $M$ at a point $p$. An element of $TM$ then is a pair $(p,\gamma)$ with $\gamma \in T_p M$.

An analogue to this appears in type theory as the **dependent pair type** (also called **dependent sum** or **$\sum$-type**): the elements of the ordinary pair type $A \times B$ are pairs $(a,b)$ with $a:A$ and $b:B$. The elements of the dependent pair type $\sum_{x:A} B(x)$ are pairs $(a,b)$ with $a:A$ and $b:B(a)$. This is achieved by the following rules:

1. **Formation rules:**

$$ \frac{\vdash A \quad x:A\vdash B(x)}{\vdash \sum_{x:A}B(x)}(\text{$\sum$-form})$$

2. **Introduction rules:**

$$ \frac{\vdash a:A \quad \vdash b:B(a)}{\vdash (a,b) :\sum_{x:A}B(x)}(\text{$\sum$-intro})$$

3. **Elimination rules:**

$$ \frac{\vdash p : \sum_{x:A}B(x)}{\vdash \mathrm{first}(p) : A }(\text{$\sum$-elim${}_1$})$$



$$\frac{\vdash p : \sum_{x:A}B(x)}{\vdash \mathrm{second}(p) : B(\mathrm{first}(p)) }(\text{$\sum$-elim${}_2$})
$$

The $\beta$- and $\eta$-rules hold analogously.

We will also always employ the **$\alpha$-conversion rule** identifying that any expressions are equivalent if they only differ up to the renaming of **bound variables**.

For instance:

$$(\lambda x.f(x)) \equiv (\lambda y.f(y))$$

$$\left(\sum_{a:A} B(a)\right) \equiv \left(\sum_{x:A} B(x)\right)$$

In particular, we will silently use **capture-avoiding substitution** in case of naming conflicts:

1. Naive substitution produces errors: $(\lambda y.x)[y/x] \equiv \lambda y.y \quad (!!)$

2. As a fix, rename the conflicting bound variable: $(\lambda y.x)[y/x]  \equiv (\lambda z.x)[y/x]  \equiv \lambda z.y$

A proper systematic treatment of variables in type theory requires extra care and is beyond the scope of our lecture.

In analogy to the notion of the total space $E$ of a bundle $p : E \to B$, given a family $B : A \to \mathcal U$, we call the type $\sum_{x:A} B(x)$ the **total type** of the family $B$:

```rzk
#def total-type (A : U) (B : A → U)
  : U
  := Σ (a : A) , B a
```

To produce a term out of the total type $\sum_{x:A} B(x)$ into any type $C$ it suffices to have a dependent function $f : \prod_{a:A} B(a) \to C$. This is called the **recursion principle for $\sum$-types**:

```rzk
#def rec-Sigma (A : U) (B : A → U) (C : U) (f : (a : A) → B a → C)
  : total-type A B → C
  := ?
```

Note that we have $\lambda$-abstracted over a term in constructor-form `(a , b)` rather than an anonymous term `p` in `Σ (a : A) , B a`. This useful technique supported by Rzk is called **pattern-matching**, making many proofs easier to write and read.

Similarly, we also can prove the **induction principle for $\sum$-types** where $C$ is not a constant type but a family over $\sum_{x:A} B(x)$:

```rzk
#def ind-Sigma (A : U) (B : A → U) (C : (total-type A B) → U) (f : (a : A) → (b : B a) → C (a , b))
  : ( z : total-type A B) → C z
  := ?
```

Interestingly, we can now prove a version of the axiom of choice: let $A$ and $B$ be types and $R : A \to B \to \mathcal U$ a "relation". Assume that for all $x : A$ there is a $y : B$ such that $R x y$ holds. Then there should exist a "choice function" $f : A \to B$ such that for all $x:A$ we have $Rx (fx)$.

In total, what we would like is a term as follows:

$$ \mathrm{ac}_{A,B,R} : \left( \prod_{x:A} \sum_{y:B} Rxy\right) \to \left( \sum_{f : A \to B} \prod_{x:A} R x (fx)) \right) $$

```rzk
#def ac (A B : U) (R : A → B → U) (g : (x : A) → Σ (y : B) , R x y)
  : Σ ( f : A → B) , (x : A) → R x (f x)
  := ?
```

## §1.5. Propositions as types

As suggested by the above axiom of choice, a fruitful way to think about types is as logical propositions, and type formers as logical connectives.

It is crucial to note that not every type is a proposition but for the moment we don't need to worry about that.

Let's make the above precise. A logical proposition should be interpreted as a type. A proof or witness of this proposition should give rise to a term of this type. The type formers will then lift correspondingly. E.g., if $A$ and $B$ correspond to propositions, the type $A \times B$ should correspond to their conjunction: its terms are of the form $(a , b) : A \times B$, i.e., they are *pairs* of a proof (or witness or evidence) of $A$ and a proof of $B$.

This interpretation is known as the **Curry--Howard correspondence**, closely related to the **Brouwer--Heyting--Kolmogorov (BHK) interpretation** in constructive mathematics.

| Logic                                        | Type theory                           | Rzk               |
|----------------------------------------------|---------------------------------------|-------------------|
| proposition $A$                              | type $A$                              | `A`               |
| witness of $A$                              | term $x : A$                              | `a : A`               |
| implication $A \implies B$                   | function type $A \to B$               | `A → B`           |
| conjunction $A \land B$                      | product type $A \times B$             | `prod A B`        |
| disjunction $A \lor B$                       | coproduct type $A + B$                | `coprod A B`      |
| true proposition $\top$                      | unit type $\mathbf{1}$                | `Unit`            |
| false proposition $\bot$                     | zero type $\mathbf{0}$                | `Void`            |
| universal quantification $\forall x, B(x)$   | dep. function type $\prod_{x:A} B(x)$ | `(x : A) → B(x)`  |
| existential quantification $\exists x, B(x)$ | dep. pair type $\sum_{x : A} B(x)$    | `Σ (x : A) , B x` |

Propositions as types and the Curry--Howard correspondence are important paradigms all through constructive mathematics and functional programming. It allows for constructive proofs of logical laws. E.g., the *modus ponens* law says:

*If $A$ is true, and if $A$ implies $B$, then $B$ is true.*

Translating this via the Curry--Howard correspondence means we have to give a function:

$$\text{modus-ponens}_{A,B} : \left(A \times (A \to B)\right) \to B$$

Can you solve the following goal in Rzk?

```rzk
#def modus-ponens (A B : U)
  : prod A (A → B) → B
  := ?
```


## §1.6. Identity types

In homotopy type theory, the notion of identity is **intensional**, meaning we would like to keep track of *how* and not just *if* two terms of a type are equal. Homotopy type theory supports identity types due to Martin-Löf which are defined as follows:

**1. Formation rule:**

$$ \frac{\vdash A \quad \vdash x,y:A}{\vdash x =_A y}(\text{$=$-form})$$

For a type $A$ and terms $x,y:A$ there is the identity type $x =_A y$ (it could be empty). We also call $x =_A y$ a **path type** and its inhabitants **paths**.

**2. Introduction rule:**

$$ \frac{\vdash A \quad \vdash x:A}{\vdash \mathtt{refl}_x : x =_A x}(\text{$=$-intro})$$

Every term is canonically identical to itself.

**3. Elimination rule:**

$$ \frac{\vdash A \quad \vdash x:A
\quad \vdash C : \prod_{y : A} (x = y) \to \mathcal U \quad \vdash d : C(x,\mathtt{refl}_x)}{y:A , p : (x=_Ay)\vdash \text{ind-path}_{x,d}(y,p) : C(y,p)}(\text{$=$-elim})$$

This rule might make you wonder. It is a strong principle that says: given a family $C : \prod_{y : A} (x = y) \to \mathcal U$, we can get a section of $C$ from just a single term of the fiber $C(x,\mathtt{refl}_x)$.

**3. Computation rule:**

$$\text{ind-path}_{x,d}(x,\mathtt{refl}_x) \equiv d \quad  (\text{$=$-comp})$$

This rule says that the induction term generated from $d$ strictly extends it.

Both the constructor and eliminator are primitives in Rzk. We can state the corresponding rules using wrappers.

Namely, the introduction rule can be stated as:

```rzk
#def intro-path
     ( A : U)
     ( x : A)
  : ( x =_{A} x)
  := ?
```

Both in type-theoretic and Rzk syntax we can drop the subscript, and simply write $x = y$ or `x = y`, resp.

The elimination rule is captured by the following definition:

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

What is intriguing about the Martin-Löf identity types and the elimination rule is that they allow for proving that the dependent identity type $x,y:A \vdash x = y$ really behaves like equality should in that it satisfies the following laws. Let $x,y,z:A$ be terms. Then:

* **reflexivity:** $\mathtt{refl}_x : x=x$
* **symmetry:** $\mathrm{rev}_{x,y} : (x = y) \to (y = x)$
* **transitivity:**
 $\mathrm{concat}_{x,y,z} : (x = y) \to (y = z) \to (x = z)$
* **congruence:** Let $f : A \to B$ be a function. Then there is a function $\mathrm{ap}_{f,x,y} : (x=_Ay) \to (f(x) =_B f(y))$
* **transport:** Let $x :A \vdash B(x)$ be a family and $p : (x =_A y)$ be a path. Then there is a function $\mathrm{tr}_{B,p} : B(x) \to B(y)$.

substitution is transport: a property that holds at x is carried to y.

You can prove these later in the exercises. To give you a taste, here are two examples:

* **Symmetry:**
```rzk
#def rev
    ( A : U)
    ( x : A)
    ( y : A)
    ( p : x = y)
  : y = x
  := ind-path A x (\ y → \ p → (y = x)) refl y p
```

* **Transport:**
```rzk
#def transport (A : U) (B : A → U) (x y : A) (p : x = y) (b : B x)
  : B y
  := ind-path A x (\ y → \ p → B y) b y p
```

Do you notice the power of path induction? It seems hard to define functions depending on arbitrary paths in such an abstract setting, but path induction lets us reduce this to the case of reflexivity which makes giving the actual function seem trivial.

Moreover, we are getting closer to the homotopical picture of our type theory: we can study types through their identity types, just as we study spaces through their path spaces in homotopy theory.

In particular, since every type family supports path transport they behave like a **fibration** in the topological space. Informally speaking, in homotopy theory a fibration is a continuous map $\pi : E \to B$ such that every path $p : x \rightsquigarrow y$ in $B$ gives rise to a continuous function $p_* : E_x \to E_y$.

The consequences of path induction go even further: not only do we have these basic laws, or better **operations**, for the identity types. We also can show that they interact with each other in a meaningful way. Namely, we get laws such as the following:

$$\mathrm{concat}_{x,y,y}(p,\mathtt{refl}_y) = p$$

But this is not just an equation; it's a type itself! So saying that this law holds means to construct a term:

$$\text{right-unit}_{x,y,p} : \mathrm{concat}_{x,y,y}(p,\mathtt{refl}_y) = p$$

More explicitly, this term is exhbited as a higher "path between paths:"

$$\text{right-unit}_{x,y,p} : \mathrm{concat}_{x,y,y}(p,\mathtt{refl}_y) =_{(x=_Ay)} p$$

Again, we construct such a term by path induction:

```rzk
#def right-unit (A : U) (x y : A) (p : x = y)
  : concat A x y y p refl = p
  := (ind-path A x (\ y → \ p → concat A x y y p refl = p) refl y p)
```

Similarly, one can prove the left unit law as well as associativity (see the exercises/Yoneda game):

$$ \text{concat-assoc} : \prod_{x,y,z,w : A} \prod_{p : (x=y)} \prod_{q : (y = z)} \prod_{r : (z = w)} \mathrm{concat}_{x,z,w}(\mathrm{concat}_{x,y,z}(p,q), r) = \mathrm{concat}_{x,y,w}(p,\mathrm{concat}_{y,z,w}(q,r))$$

## §1.7. Types as $\infty$-groupoids

The rules for identity types go back to Per Martin-Löf and his 1975 seminal paper "An Intuitionistic Theory of Types." This work sparked the question if one could derive the principle of **uniqueness of identity proofs (UIP)**, i.e., if one could construct a term of the following type:

$$ \prod_{A : \mathcal U} \prod_{x,y:A} \prod_{p,q : (x=_A y)} \left( p=_{(x =_A y)} q\right)$$

This question was answered in the negative by Martin Hofmann and Thomas Streicher and their **groupoid model** from 1993: a type is interpreted as a groupoid and identity types are interpreted as the automorphisms of the respective elements. Since these need not necessarily be singletons UIP is not validated in this model, hence cannot be derivable in the theory.

However, given that all the higher identity types are themselves groupoids and that the groupoid laws in the theory don't hold strictly but, in turn, only up to higher identities, one might ask for the types to be modeled not just as groupoids but weak infinite-dimensional groupoids aka **$\infty$-groupoids**. A well-known version of $\infty$-groupoids is the notion of a Kan complex (cf. Nima's preview today and lecture tomorrow).

Indeed, this was suggested independently by Vladimir Voevodsky and Streicher in 2006, and fully developed by Chris Kapulkin, Peter Lumsdaine, and Voevodsky. In that sense, Kan complexes present the "standard model" of HoTT: a type is a Kan complex aka $\infty$-groupoid aka a topological space up to homotopy.

This is by far not the only model: after several generalizations by various people, Michael Shulman showed in 2019 that homotopy type theory can be interpreted in any **$\infty$-topos**, i.e., any higher sheaf category (a sheaf is an important generalization of a space of functions, omnipresent in algebraic geometry and topology).

We will not go into details about these models but outline below how this presents a vast extension of the propositions-as-types paradigm:

**Curry--Howard--Voevodsky correspondence:**

 Type theory                | Rzk                                     | Logic                | set theory                        | homotopy theory     |
|----------------------------|-----------------------------------------|----------------------|-----------------------------------|---------------------|
| $A$                        | `A`                                     | proposition          | set                               | space               |
| $x:A$                      | `x:A`                                   | witness              | element                           | point               |
| $\mathbf{0}, \mathbf{1}$   | `Void`, `Unit`                          | $\top$, $\bot$       | $\emptyset$, $\{\emptyset\}$      | $\emptyset$, $\ast$ |
| $A \times B$               | `prod A B`                              | $A \land B$          | set of ordered pairs              | product space       |
| $A + B$                    | `coprod A B`                            | $A \lor B$           | disjoint union                    | coproduct           |
| $A \to B$                  | `A → B`                                 | $A \implies B$       | set of functions                  | function space      |
| $x : A \vdash B(x)$        | `B : A → U`                             | predicate $B(x)$     | family of sets                    | fibration           |
| $\prod_{x:A} B(x)$         | `(x : A) → B(x)`                        | $\forall x, B(x)$    | product                           | space of sections   |
| $\sum_{x:A} B(x)$          | `Σ (x : A) , B x`                       | $\exists x, B(x)$    | disjoint union                    | total space         |
| $x : A \vdash b(x) : B(x)$ | `b : (x : A) → B(x)`                    | parametrized witness | family of elements                | section             |
| $p : x=_A y$               | `p : x =_{A} y`                         | equality witness     | $x = y$                           | path                |
| $\sum_{x,y:A} x=_A y$      | `Σ (x y : A) , Σ (y : A) , x = _{A}  y` | equality relation    | diagonal $\{(a,a) \; \mid \; a:A\}$ | path space          |

**NB:** "Space" her can mean e.g. Kan complex, a notion of $\infty$-groupoids in simplicial sets (cf. Nima's lecture). Accordingly, fibrations are then Kan fibrations.

## §1.8. Equivalences

Given that types can be modeled as homotopy types we should be able to capture a notion of **equivalence** of types, corresponding to homotopy equivalence in the model.

As a first notion, we want to introduce **logical equivalence** of a type. We say $A$ and $B$ are logically equivalent if each admits functions to the other one:

$$ (A \leftrightarrow B) :\equiv (A \to B) \times (B \to A)$$

This means, one of the types is inhabited if and only if the other one is:

```rzk
#def iff
  ( A B : U)
  : U
  := product (A → B) (B → A)
```

Let $f, g : A \to B$ be two maps between types. A **homotopy** from $f$ to $g$ should be a pointwise equality between their images. Hence we define:

$$ \mathrm{homotopy}_{A,B}(f,g) :\equiv (f \sim g) :\equiv \prod_{x : A} (f(x) =_B g(x)) $$

In Rzk, this becomes:

```rzk
#def homotopy
  ( A B : U)
  ( f g : A → B)
  : U
  := (x : A) → f x = g x
```

Now , a map $f : A \to B$ is an **equivalence** if it comes equipped with a left inverse map (called a **retraction**) and with a right inverse map (called a **section**). Accordingly, we first define the following type witnesses that a given $f : A \to B$ is an equivalence:


$$ \text{is-equiv}_{A,B}(f) :\equiv \sum_{r : B \to A} (r \circ f \sim \mathrm{id}_A) \times
(f \circ s \sim \mathrm{id}_A)$$

Then, the type of equivalences from $A$ to $B$ is any map $f : A \to B$ together with a proof that $f$ is an equivalence:

$$ \mathrm{Equiv}(A,B) :\equiv (A \simeq B) :\equiv \sum_{f : A \to B} \text{is-equiv}_{A,B}(f) $$

In Rzk, these definitions are given as follows:

```rzk
#def is-equiv
( A B : U)
( f : A → B)
  : U
  := prod
    ( Σ ( r : B → A) , homotopy A A (\ a → r (f a)) (id A))
    ( Σ ( s : B → A) , homotopy B B (\ b → f (s b)) (id B))

#def Equiv
    ( A B : U)
  : U
  := Σ (f : A → B) , (is-equiv A B f)

#def has-section-is-equiv
  ( A B : U)
  ( f : A → B)
  ( is-equiv-f : is-equiv A B f)
  : Σ ( s : B → A) , homotopy B B (\ b → f (s b)) (id B)
  := second is-equiv-f

#def section-is-equiv
  ( A B : U)
  ( f : A → B)
  ( is-equiv-f : is-equiv A B f)
  : B → A
  := first (has-section-is-equiv A B f is-equiv-f)
```

One can prove that being an equivalent is an equivalence relation on the universe of all types. In particular, every equivalence $A \to B$ gives rise to a map $B \to A$ which is an equivalence itself.

## §1.9. Contractibility, propositions, and sets

The (higher) identity types are what gives types interesting homotopical structure. Voevodsky had the insight to stratify them into a hierarchy of $n$-types, with $n$ either being an integer with $n \geq -2$ or $n = \infty$.

We start with the lowest levels.

1. A type $A$ is **contractible** it comes with a homotopically unique term:

$$ \text{is-contr}(A) :\equiv \sum_{c : A} \prod_{x : A} (c = x) $$

2. A type $A$ is a **(mere) proposition** if any two terms in it are equal:

$$ \text{is-prop}(A) :\equiv \prod_{x, y : A} (x = y) $$

3. A type $A$ is a **set** if any two proofs of an equality are equal:

$$ \text{is-set}(A) :\equiv \prod_{x, y : A} \text{is-prop}(x = y) $$

In Rzk, these definitions read as follows:

```rzk
#def is-contr
    ( A : U)
  : U
  := Σ (c : A) , (x : A) → c = x

#def is-prop
     ( A : U)
  : U
  := (x y : A) → x = y

#def is-set
    ( A : U)
  : U
  := (x y : A) → is-prop (x = y)
```
We also say that contractible types are of **homotopy level (h-level)** $-2$, or that they are **$(-2)$-types**. For $n \geq -1$, we say that a type $A$ has **h-level** $n$ or is an **$n$-type** if for all $x,y:A$ the identity type $(x = y)$ is an $(n-1)$-type:

$$ \text{is-$n$-type}(A) :\equiv \prod_{x,y:A} \text{is-$(n-1)$-type}\left((x = y)\right) $$

One can show that the $(-1)$-types are exactly the propositions, and the $0$-types are exactly the sets.

For $n \geq 1$, the $n$-types correspond to $n$-groupoids.

Types that are not of h-level $n$ for any finite $n$ correspond to full homotopy types *aka* $\infty$-groupoids.

Indeed, any $n$-type is also an $(n+1)$-type, for all $n \geq -2$, but not the other way around.

In most cases, we will consider types that are either a priori of h-level $\infty$, or of a lower h-level such as $-2$ or $-1$.

In particular, recalling the Curry--Howard--Voevodsky correspondence, these considerations mean that this correspondence is not just a matter of the semantics chosen. Rather, we can capture the various columns internally to the theory, and consider the propositional/set-theoretic/1-groupoidal/... fragments of the full homotopy type theory.

As an example of a contractible type we can exhibit the unit type $\mathbf{1}$. Indeed, any contractible type will turn out to be equivalent to $\mathbf{1}$.


In Rzk, any two inhabitants of the unit type are *judgmentally* equal, hence they can be identified by $\mathrm{refl}$. We denote the unit type by `Unit` and its distinguished inhabitant by `unit : Unit`. Let us prove that `Unit` is contractible:

```rzk
#def is-contr-Unit
  : is-contr Unit
  := ?
```

Every contractible type is a proposition. To prove this we have to produce a function:

$$ \prod_{A : \mathcal U} \text{is-contr}(A)\to \text{is-prop}(A) $$

Let $A : \mathcal U$ and $c : \text{is-contr}(A)$. Then $c$ consists of:
* a **center of contraction** $\mathrm{first}(c): A$
* a **contracting homotopy** $\mathrm{second}(c) : \prod_{x : A} (c = x)$

We can introduce shortcuts for these:

```rzk
#def center-contraction
  ( A : U)
  ( is-contr-A : is-contr A)
  : A
  := first is-contr-A

#def homotopy-contraction
( A : U)
( is-contr-A : is-contr A)
  : ( z : A) → (center-contraction A is-contr-A) = z
  := second is-contr-A
```

To produce a witness for $A$ being a proposition we need to give a function that connects any two points via a path. But this we can extract from the contracting homotopy via concatenation and reversal.

In Rzk, this reads as follows:

```rzk
#def all-elements-equal-is-contr
  ( A : U)
  ( is-contr-A : is-contr A)
  ( x y : A)
  : x = y
  :=
    concat A x (center-contraction A is-contr-A) y
      ( rev A (center-contraction A is-contr-A) x
        ( homotopy-contraction A is-contr-A x))
      ( homotopy-contraction A is-contr-A y)
```

Notably, the properties of a type being contractible/a proposition/a set, or, of a map being an equivalence are actually properties in the sense that they are all propositions in the sense that we can construct terms of the following types:

$$\text{is-prop}\left(\text{is-contr}(A)\right)$$

$$\text{is-prop}\left(\text{is-prop}(A)\right)$$

$$\text{is-prop}\left(\text{is-set}(A)\right)$$

$$\text{is-prop}\left(\text{is-equiv}(f)\right)$$

That means, any two witnesses/proofs/pieces of evidence that any of these properties hold must be equal to each other to homotopy. A type can be contractible/a proposition/a set in essentially at most one way; there is no higher structure necessary.


One can furthermore prove:

* If a proposition is inhabited then it is a contractible.
* A type is contractible if and only if it is equivalent to the unit type.
* A type $A$ is a proposition if and only if $A \to \text{is-contr}(A)$; in other words if, whenever $A$ is inhabited it is contractible.

For this, we need the notion of **preimage** or **fiber** of a map. If $f : A \to B$ is a map between types and $y : B$ a point then we call

$$ \mathrm{preimage}_{A,B}(f,y) :\equiv \mathrm{fib}_{A,B}(f,y) f^{-1}(y) :\equiv \sum_{x : A} f(x) =_B y $$

the **preimage** or **fiber** of $f$ at $y$. Its terms are pairs $(x,p)$ where $x : A$ and $p : f(x) =_B y$ a path from $f(x)$ to $y$. This is exactly the synthetic version of the notion of homotopy fiber.

```rzk
#def fib
  ( A B : U)
  ( f : A → B)
  ( b : B)
  : U
  := Σ (a : A) , (f a = b)
```

With some work one can then prove that a map $f : A \to B$ is an equivalence if and only if all of its fibers are contractible:

$$\text{is-equiv}(f) \simeq \prod_{y : B} \text{is-contr}(f^{-1}(y))$$

## §1.10. Function extensionality

When are two functions to be considered equal, as terms of a function type? By path induction, equality implies pointwise equality.

Let $f,g : X \to A$ be functions. Then, we get a map

$$ (f =_{X \to A} g) \to \left( \prod_{x:X} f(x) =_A g(x) \right), $$

or, more generally, if $A : X \to \mathcal U$ is a type family, and $f,g : \prod_{x:X} A(x)$ are sections:

$$(f =_{\prod_{x:X} A(x)} g) \to \left( \prod_{x:X} f(x) =_{A(x)} g(x) \right) $$

This is defined as follows:

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
```

But this map need not be an equivalence in general! Thus, we will assume this as a principle:

```rzk
#def FunExt
  : U
  :=
    ( X : U)
  → ( A : X → U)
  → ( f : (x : X) → A x)
  → ( g : (x : X) → A x)
  → is-equiv (f = g) ((x : X) → f x = g x) (htpy-eq X A f g)

#assume funext : FunExt
```

## Bibliography

Some suggested further reading:

* Carlo Angiuli and Daniel Gratzer. *Principles of Dependent Type Theory*. Cambridge University Press, forthcoming. [https://carloangiuli.com/papers/type-theory-book.pdf](https://carloangiuli.com/papers/type-theory-book.pdf)
* Steve Awodey. Type theory and homotopy. In Peter Dybjer, Sten Lindström, Erik Palmgren, and Göran Sundholm (eds.), *Epistemology versus Ontology: Essays on the Philosophy and Foundations of Mathematics in Honour of Per Martin-Löf*, Logic, Epistemology, and the Unity of Science 27, Springer, 2012, pp. 183–201. [arXiv:1010.1810](https://arxiv.org/abs/1010.1810)
* Steve Awodey and Michael A. Warren. Homotopy theoretic models of identity types. *Mathematical Proceedings of the Cambridge Philosophical Society* **146** (2009), no. 1, 45–55. [arXiv:0709.0248](https://arxiv.org/abs/0709.0248)
* Martin Hofmann and Thomas Streicher. The groupoid model refutes uniqueness of identity proofs. In *Proceedings of the Ninth Annual IEEE Symposium on Logic in Computer Science (LICS 1994)*, IEEE Computer Society Press, 1994, pp. 208–212.
* Krzysztof Kapulkin and Peter LeFanu Lumsdaine. The simplicial model of Univalent Foundations (after Voevodsky). *Journal of the European Mathematical Society* **23** (2021), no. 6, 2071–2126. [arXiv:1211.2851](https://arxiv.org/abs/1211.2851)
* Nikolai Kudasov, Violetta Sim, and Benedikt Ahrens. Rzk: a proof assistant for synthetic $\infty$-categories. Preprint, 2026. [arXiv:2607.12207](https://arxiv.org/abs/2607.12207)
* Emily Riehl. *Homotopy Type Theory*. Lecture notes for Math 721, Johns Hopkins University, Fall 2021. [https://github.com/emilyriehl/721](https://github.com/emilyriehl/721)
* Emily Riehl. On the $\infty$-topos semantics of homotopy type theory. Lecture notes, Logic and Higher Structures, CIRM–Luminy, 2022. [arXiv:2212.06937](https://arxiv.org/abs/2212.06937)
* Egbert Rijke. *Introduction to Homotopy Type Theory*. Cambridge Studies in Advanced Mathematics. Cambridge University Press, 2025. Also [arXiv:2212.11082](https://arxiv.org/abs/2212.11082).
* Michael Shulman. All $(\infty,1)$-toposes have strict univalent universes. Preprint, 2019. [arXiv:1904.07004](https://arxiv.org/abs/1904.07004)
* Michael Shulman. Homotopy type theory: the logic of space. In Mathieu Anel and Gabriel Catren (eds.), *New Spaces in Mathematics: Formal and Conceptual Reflections*, Cambridge University Press, 2021, pp. 322–404. [arXiv:1703.03007](https://arxiv.org/abs/1703.03007)
* Thomas Streicher. A model of type theory in simplicial sets: A brief introduction to Voevodsky's homotopy type theory. *Journal of Applied Logic* **12** (2014), no. 1, 45–49. [https://www2.mathematik.tu-darmstadt.de/~streicher/sstt.pdf](https://www2.mathematik.tu-darmstadt.de/~streicher/sstt.pdf)
* The Univalent Foundations Program. *Homotopy Type Theory: Univalent Foundations of Mathematics*. Institute for Advanced Study, 2013. [https://homotopytypetheory.org/book/](https://homotopytypetheory.org/book/)

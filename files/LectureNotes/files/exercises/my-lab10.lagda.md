# Week 10 - Lab Sheet

```agda
module exercises.my-lab10 where

open import prelude

open import Bool
open import decidability
open import Fin
open import isomorphisms
open import List-functions
open import sorting
open import strict-total-order
open import natural-numbers-functions
open import exercises.homework9-solutions
```

## Strict total order on finite types

You are going to define a strict total order on `Fin n` for every natural number
`n`.

### Exercise 1.1

For any `n : ℕ`, the type `Fin n` has decidable equality.

**Prove** this fact by first proving the lemma `[Fin n ]-suc-is-injective`.

```agda
[Fin_]-suc-is-injective : (n : ℕ) (x y : Fin n)
                        → _≡_ {Fin _} (suc x) (suc y) -- suc x ≡ suc y
                        → x ≡ y
[Fin n ]-suc-is-injective x .x (refl .(suc x)) = refl x

[Fin_]-decidable : (n : ℕ) → has-decidable-equality (Fin n)
[Fin (suc n) ]-decidable zero zero = inl (refl zero)
[Fin (suc n) ]-decidable zero (suc y) = inr (λ {()})
[Fin (suc n) ]-decidable (suc x) zero = inr (λ {()})
[Fin (suc n) ]-decidable (suc x) (suc y) with IH
  where
    IH : is-decidable (x ≡ y)
    IH = [Fin n ]-decidable x y
[Fin suc n ]-decidable (suc x) (suc y) | inl x=y
 = inl (ap suc x=y)
[Fin suc n ]-decidable (suc x) (suc y) | inr ¬x=y
 = inr (λ sx=sy → ¬x=y ([Fin n ]-suc-is-injective x y sx=sy))
```

### Exercise 1.2

**Define** the strict total order and **prove** that it is irreflexive,
transitive and connected.

```agda
[Fin_]_<_ : (n : ℕ) → (x y : Fin n) → Type
[Fin suc n ] x < zero = 𝟘
[Fin suc n ] zero < suc y = 𝟙
[Fin suc n ] suc x < suc y = [Fin n ] x < y

[Fin_]-irreflexive : (n : ℕ) → (x : Fin n) → ¬ ([Fin n ] x < x)
[Fin suc n ]-irreflexive zero ()
[Fin suc n ]-irreflexive (suc x) l = [Fin n ]-irreflexive x l

[Fin_]-transitive : (n : ℕ) → {x y z : Fin n}
                  → [Fin n ] x < y → [Fin n ] y < z → [Fin n ] x < z
[Fin suc n ]-transitive {zero} {y} {suc z} x<y y<z = ⋆
[Fin suc n ]-transitive {suc x} {suc y} {suc z} x<y y<z
 = [Fin n ]-transitive {x} {y} {z} x<y y<z

[Fin_]-connected : (n : ℕ) → {x y : Fin n}
                 → ¬ (x ≡ y) → ([Fin n ] x < y) ∔ ([Fin n ] y < x)
[Fin suc n ]-connected {zero} {zero} ¬x=y = inl (¬x=y (refl zero)) 
[Fin suc n ]-connected {zero} {suc y} ¬x=y = inl ⋆
[Fin suc n ]-connected {suc x} {zero} ¬x=y = inr ⋆
[Fin suc n ]-connected {suc x} {suc y} ¬sx=sy
 = [Fin n ]-connected {x} {y} (λ x=y → ¬sx=sy (ap suc x=y))

Fin-STO : (n : ℕ) → StrictTotalOrder (Fin n)
Fin-STO n = record
              { _<_         = [Fin n ]_<_
              ; decidable   = [Fin n ]-decidable
              ; irreflexive = [Fin n ]-irreflexive
              ; transitive  = [Fin n ]-transitive
              ; connected   = [Fin n ]-connected
              }
```

## Permutations and length

In this exercise you will prove that if two lists are permutations of each
other, then they have the same length.

In doing so, you may use the following fact without having to prove it:
```agda-code
fact : {X Y : Type} → 𝟙 ∔ X ≅ 𝟙 ∔ Y → X ≅ Y
```

We assume this `fact` without proving it by using an anonymous module.

You are encouraged to think about how you would prove `fact` and why it may
require some work to formalize this argument in Agda.


```agda
module _
        (fact : {X Y : Type} → 𝟙 ∔ X ≅ 𝟙 ∔ Y → X ≅ Y)
       where

 open _≅_
 open _IsPermutationOf_
```

### Exercise 2.1

**Prove** that having an isomorphism on the positions of two lists implies that
  the lists have equal length.

```agda
 Pos-iso-same-length : {A : Type} (xs ys : List A)
                     → Pos xs ≅ Pos ys → length xs ≡ length ys
 Pos-iso-same-length [] [] iso = refl zero
 Pos-iso-same-length [] (x :: ys) (Isomorphism f (Inverse g η ε))
  = 𝟘-elim (g (inl ⋆))
 Pos-iso-same-length (x :: xs) [] (Isomorphism f (Inverse g η ε))
  = 𝟘-elim (f (inl ⋆))
 Pos-iso-same-length (x :: xs) (y :: ys) iso
  = ap suc (Pos-iso-same-length xs ys (fact iso))
```

### Exercise 2.2

**Conclude** that if two lists are a permutation of each other, then they have the
same length.

```agda
 permutations-have-same-length : {A : Type} (xs ys : List A)
                               → xs IsPermutationOf ys → length xs ≡ length ys
 permutations-have-same-length xs ys
  record { pos-iso = pos-iso ; inhab-eq = inhab-eq }
  = Pos-iso-same-length xs ys pos-iso
```

## Adding minimal and maximal elements to an order

In this exercise, we will define a function that takes a `StrictTotalOrder` and
transforms it into one with minimum and maximum elements.

This is often convenient in practice, for example, in [Dijkstra's
algorithm](https://en.wikipedia.org/wiki/Dijkstra%27s_algorithm#Pseudocode).

### Exercise 3.1

Let `X` be a type with a strict total order `_<_`. To add minimum and maximum
elements to `X`, we will use the carrier set `X + Bool` in which `inr false`
will represent the minimum element and `inr true` will represent the maximum
element.

The next task is to define the “lifting” of an order `_<_` on type `X` to `X +
Bool` containing min and max.

**Define** the following `lift` function:

```agda
lift : {X : Type} → (_<_ : X → X → Type) → X ∔ Bool → X ∔ Bool → Type
lift _<_ x           (inr false) = 𝟘
lift _<_ (inl x)     (inl y)     = x < y
lift _<_ (inr true)  (inl y)     = 𝟘
lift _<_ (inr false) (inl y)     = 𝟙
lift _<_ (inl x)     (inr true)  = 𝟙
lift _<_ (inr true)  (inr true)  = 𝟘
lift _<_ (inr false) (inr true)  = 𝟙
```

You should ensure that, under your definition of `lift`, `min < x` for all `x`
except `min` and and `x < max` for all `x` except `max`.

### Exercise 3.2

You must now prove that the lifting you defined gives rise to another strict
total order.

**Complete** the implementation of the `add-bounds` function that takes a
`StrictTotalOrder` `sto` and constructs the lifted strict total order with
minimum and maximum elements.

*Hint*: For `decidable↑` it is convenient to use `+-has-decidable-equality` from
 week 9's homework sheet, the solutions of which are already imported for you.

```agda
bool-has-decidable-equality : has-decidable-equality Bool
bool-has-decidable-equality true  true  = inl (refl true)
bool-has-decidable-equality true  false = inr (λ ())
bool-has-decidable-equality false true  = inr (λ ())
bool-has-decidable-equality false false = inl (refl false)

add-bounds : {X : Type} → StrictTotalOrder X → StrictTotalOrder (X ∔ Bool)
add-bounds {X} sto = record
                      { _<_         = _<↑_
                      ; decidable   = decidable↑
                      ; irreflexive = irreflexive↑
                                      -- Unfortunately, implicit arguments have
                                      -- to be η-expanded here to prevent yellow
                                      -- and it's not clear why this is the
                                      -- case.
                      ; transitive  = λ {x} {y} {z} → transitive↑ {x} {y} {z}
                      ; connected   = connected↑
                      }
 where
  open StrictTotalOrder sto

  _<↑_ : X ∔ Bool → X ∔ Bool → Type
  _<↑_ = lift _<_

  decidable↑ : has-decidable-equality (X ∔ Bool)
  decidable↑ (inl x) (inl y) with decidable x y
  decidable↑ (inl x) (inl y) | inl x=y
   = inl (ap inl x=y)
  decidable↑ (inl x) (inl y) | inr ¬x=y
   = inr (λ { (refl .(inl x)) → ¬x=y (refl x)})
  decidable↑ (inl x) (inr y) = inr (λ {()})
  decidable↑ (inr x) (inl y) = inr (λ {()})
  decidable↑ (inr x) (inr y) with bool-has-decidable-equality x y
  decidable↑ (inr x) (inr .x) | inl (refl .x)
   = inl (refl (inr x))
  decidable↑ (inr x) (inr y)  | inr ¬x=y
   = inr (λ {(refl .(inr x)) → ¬x=y (refl x)})

  irreflexive↑ : (x : X ∔ Bool) → ¬ (x <↑ x)
  irreflexive↑ (inl x) l = irreflexive x l
  irreflexive↑ (inr true) ()
  irreflexive↑ (inr false) ()

  transitive↑ : {x y z : X ∔ Bool} → x <↑ y → y <↑ z → x <↑ z
  transitive↑ {inl x}     {inl y}     {inl z}     x<y y<z = transitive x<y y<z
  transitive↑ {inl x}     {inl y}     {inr true}  x<y y<z = ⋆
  transitive↑ {inl x}     {inr true}  {inl z}     x<y ()
  transitive↑ {inl x}     {inr false} {inl z}     ()  y<z
  transitive↑ {inl x}     {inr true}  {inr false} x<y ()
  transitive↑ {inl x}     {inr false} {inr false} x<y ()
  transitive↑ {inr false} {inl y}     {inl z}     x<y y<z = ⋆
  transitive↑ {inr false} {inl y}     {inr true}  x<y y<z = ⋆
  transitive↑ {inr true}  {inr true}  {inl z}     x<y ()
  transitive↑ {inr true}  {inr false} {inl z}     ()  y<z
  transitive↑ {inr false} {inr y}     {inl z}     x<y y<z = ⋆
  transitive↑ {inr true}  {inr true}  {inr true}  x<y ()
  transitive↑ {inr true}  {inr false} {inr true}  ()  y<z
  transitive↑ {inr false} {inr y}     {inr true}  x<y y<z = ⋆
  transitive↑ {inr true}  {inr true}  {inr false} x<y ()
  transitive↑ {inr true}  {inr false} {inr false} x<y ()
  transitive↑ {inr false} {inr true}  {inr false} x<y ()
  transitive↑ {inr false} {inr false} {inr false} x<y ()

  connected↑ : {x y : X ∔ Bool} → ¬ (x ≡ y) → (x <↑ y) ∔ (y <↑ x)
  connected↑ {inl x} {inl y} ¬lx=ly with trichotomy x y
  connected↑ {inl x} {inl y} ¬lx=ly | inl x<y
   = inl x<y
  connected↑ {inl x} {inl y} ¬lx=ly | inr (inl x=y)
   = 𝟘-elim (¬lx=ly (ap inl x=y))
  connected↑ {inl x} {inl y} ¬lx=ly | inr (inr y<x)
   = inr y<x
  connected↑ {inl x} {inr true} ¬x=y = inl ⋆
  connected↑ {inl x} {inr false} ¬x=y = inr ⋆
  connected↑ {inr true} {inl y} ¬x=y = inr ⋆
  connected↑ {inr false} {inl y} ¬x=y = inl ⋆
  connected↑ {inr true} {inr true} ¬x=y = inl (¬x=y (refl (inr true)))
  connected↑ {inr true} {inr false} ¬x=y = inr ⋆
  connected↑ {inr false} {inr true} ¬x=y = inl ⋆
  connected↑ {inr false} {inr false} ¬x=y = inl (¬x=y (refl (inr false)))
```

# Homework exercises

The exercises here include the 5 exercises of Test 2 last year, and
many more that could potentially occur in a Test 2. Some of them are
rather hard. But rest reassured that there will be only one rather
hard exercise in Test 2, on just hard, and three easy and medium.

## Prove an isomorphism

The type `ℕ` of natural numbers contains _countably infinite_ inhabitants. But
the type `𝟙 ∔ ℕ` also contains the same number of inhabitants which means that
these types are actually isomorphic.

**Prove** this fact.

```agda
ℕ-is-isomorphic-to-𝟙∔ℕ : ℕ ≅ 𝟙 ∔ ℕ
ℕ-is-isomorphic-to-𝟙∔ℕ = record { bijection = f ; bijectivity = f-is-bijection }
 where
  f : ℕ → 𝟙 ∔ ℕ
  f zero    = inl ⋆
  f (suc n) = inr n

  g : 𝟙 ∔ ℕ → ℕ
  g (inl ⋆) = zero
  g (inr n) = suc n

  gf : (g ∘ f) ∼ id
  gf zero    = refl zero
  gf (suc n) = refl (suc n)

  fg : (f ∘ g) ∼ id
  fg (inl ⋆) = refl (inl ⋆)
  fg (inr n) = refl (inr n)

  f-is-bijection : is-bijection f
  f-is-bijection = record { inverse = g ; η = gf ; ε = fg }
```

## Prove a property of the length function

In [List-functions.lagda.md](../List-functions.lagda.md) we defined the


```agda-code
length : {A : Type} → List A → ℕ
length []        = 0
length (x :: xs) = 1 + length xs
```

A downside of this definition is that it is not tail-recursive and therefore not
very efficient. One way to have a tail-recursive computation of the length of a
list is to introduce an accumulating parameter.

We define the functions

```agda
length-aux : {A : Type} → List A → ℕ → ℕ
length-aux []        k = k
length-aux (x :: xs) k = length-aux xs (suc k)

length-tail-rec : {A : Type} → List A → ℕ
length-tail-rec xs = length-aux xs 0
```

**Prove** the following lemma about `length-aux`

```agda
length-aux-lemma : {A : Type} (xs : List A) (k : ℕ)
                 → length-aux xs k ≡ length xs + k
length-aux-lemma [] k = refl k
length-aux-lemma (x :: xs) k = 
   length-aux xs (suc k) ≡⟨ length-aux-lemma xs (suc k) ⟩
   length xs + suc k     ≡⟨ +-step (length xs) k ⟩
   suc (length xs + k)   ∎
```

and use it to **conclude** that `length-tail-rec` is correct (in the sense that
it computes the same thing as `length`):

```agda
length-tail-rec-is-correct : {A : Type} (xs : List A) → length-tail-rec xs ≡ length xs
length-tail-rec-is-correct xs = 
   length-aux xs 0  ≡⟨ length-aux-lemma xs 0 ⟩
   length xs + zero ≡⟨ +-comm (length xs) zero ⟩
   length xs        ∎

```

*Hint*: You can use `length-aux-lemma` in solving `length-is-correct`, even if
you don't manage to prove `length-aux-lemma`.

## Mapping non-decreasing functions

A function `f : X → Y` between two strict total orders `(X,<[X])` and `(Y,<[Y])`
is said to be *non-decreasing* if whenever `x <[X] x'` then either `f x' ≡ f x`
or `f x <[Y] f x'`.

We write this in Agda as follows

```agda
module _
        {X : Type}
        {Y : Type}
        (σ : StrictTotalOrder X)
        (τ : StrictTotalOrder Y)
       where

 open StrictTotalOrder

 _<[X]_ : X → X → Type
 _<[X]_ = _<_ σ
 _<[Y]_ : Y → Y → Type
 _<[Y]_ = _<_ τ

 is-non-decreasing : (X → Y) → Type
 is-non-decreasing f = (x x' : X) → x <[X] x'
                                  → (f x' ≡ f x) ∔ (f x <[Y] f x')
```

**Prove** that if `f` is a non-decreasing function, then `map f xs` is sorted
whenever the input list `xs` is sorted:

```agda
 map-of-non-decreasing-preserves-sorted : (f : X → Y) → is-non-decreasing f
                                        → (xs : List X) → Sorted σ xs
                                        → Sorted τ (map f xs)
 map-of-non-decreasing-preserves-sorted f m []              nil-sorted       = nil-sorted
 map-of-non-decreasing-preserves-sorted f m (x :: [])       sing-sorted      = sing-sorted
 map-of-non-decreasing-preserves-sorted f m (x :: .x :: xs) (adj-sorted s (inl (refl .x)))
  = adj-sorted (map-of-non-decreasing-preserves-sorted f m (x :: xs) s) (inl (refl (f x)))
 map-of-non-decreasing-preserves-sorted f m (x :: x' :: xs) (adj-sorted s (inr x<x'))
  = adj-sorted (map-of-non-decreasing-preserves-sorted f m (x' :: xs) s) (m x x' x<x')
```

## Properties of trees

We define a type of binary trees with nodes storing values:

```agda
data BinTree (X : Type) : Type where
 Leaf : BinTree X
 Node : BinTree X → X → BinTree X → BinTree X
```

For example,

```agda
example-BinTree : BinTree ℕ
example-BinTree = Node (Node Leaf 9 (Node Leaf 4 Leaf)) 17 (Node Leaf 3 Leaf)
```

represents the binary tree
```picture
          17
          / \
         /   \
        /     \
       9       3
      / \     / \
         4
        / \
```

We can define *binary search trees* as follows:

1. A leaf is a binary search tree.
1. If `l` and `r` are binary search trees, and every node of `l` is strictly
smaller than `x`, and every node of `r` is strictly bigger than `x`, then
`Node l x r` is a binary search tree.

The tree above is *not* a binary search tree, because (for example) 3 is not
greater than or equal to 17.

But the tree
```picture
           9
          / \
         /   \
        /     \
       3      17
      / \     / \
         4
        / \
```
is an example of a binary search tree.


### Order on trees

Given a type `X` with a strict total order, we ask you to **define** two predicates
`all-smaller : BinTree X → X → Type` and `all-bigger : BinTree X → X → Type`
such that

1. We have that `all-smaller t x` if all the nodes in the binary tree `t` are
stricly smaller than `x`.
1. We have that `all-bigger t x` if all the nodes in the binary tree `t` are
strictly bigger than `x`.

```agda
all-smaller : {X : Type} (τ : StrictTotalOrder X) → BinTree X → X → Type
all-smaller τ Leaf x = 𝟙
all-smaller {X} τ (Node l y r) x = all-smaller τ l x × (y <x x) × all-smaller τ r x
 where
  open StrictTotalOrder

  _<x_ : X → X → Type
  _<x_ = _<_ τ

all-bigger : {X : Type} (τ : StrictTotalOrder X) → BinTree X → X → Type
all-bigger τ Leaf x = 𝟙
all-bigger {X} τ (Node l y r) x = all-bigger τ l x × (x <x y) × all-bigger τ r x
 where
  open StrictTotalOrder

  _<x_ : X → X → Type
  _<x_ = _<_ τ
```


### Binary search trees

Given a type `X` with a strict total order, we ask you to **define** a predicate
`is-bst : BinTree X → Type` such that `is-bst t` expresses that the binary tree
`t` is a binary search tree.

*Hint:* You will find it helpful to use the predicates from the previous part, even if you did not finish defining them.

### Write your solutions here.

For both parts, you can use `data` or instead a recursive definition, as you prefer.

```agda
module _
        {X : Type}
        (σ : StrictTotalOrder X)
       where

 open StrictTotalOrder σ

 is-bst : BinTree X → Type
 is-bst Leaf = 𝟙
 is-bst (Node l x r) = is-bst l × is-bst r × all-smaller σ l x × all-bigger σ r x
```

## Cantor's diagonalization

The [famous diagonalisation argument of
Cantor](https://en.wikipedia.org/wiki/Cantor%27s_diagonal_argument)
was used to show that `ℕ → Bool` _does not_ have the same number of
inhabitants as `ℕ`. This means an isomorphism `ℕ ≃ ℕ → Bool` cannot
exist. Your task is to prove this in the following steps.

### Construct the diagonal map

A sequence of booleans is just a function `t : ℕ → Bool`. The terms of
the sequence `t` are `t 0`, `t 1`, `t 2` , ⋯.

Now suppose you have a sequence of sequences of booleans. This is just a function `s : ℕ → (ℕ → Bool)`. The first sequence is `s 0`, the second one is `s 1` and so on. Here is an example:

![famous diagonalisation argument of
Cantor](diag.svg)

Your task is, given `s : ℕ → (ℕ → Bool)`, produce a sequence `diag s : ℕ → Bool` such that `diag s` is different from `s n` for every `n : ℕ`. Use the picture to figure out how to define `diag`:

```agda
diag : (ℕ → (ℕ → Bool)) → (ℕ → Bool)
diag s n = not (s n n)
```

Now prove that this works:
```agda
not-not-equal : (b : Bool) → ¬ (not b ≡ b)
not-not-equal true  = λ {()}
not-not-equal false = λ {()}

diag-correct : (s : ℕ → (ℕ → Bool))
             → (n : ℕ) → ¬ (diag s ∼ s n)
diag-correct s n x = not-not-equal (s n n) (x n)
```

## Use it to prove the following impossibility result

Use the functions defined above, even if you did not finish them, to complete the
proof that there can be no isomorphism between `ℕ` and `ℕ → Bool`.

```agda
ℕ≃ℕ→Bool-is-impossible : ¬ (ℕ ≅ (ℕ → Bool))
ℕ≃ℕ→Bool-is-impossible (Isomorphism f (Inverse g gf fg))
 = diag-correct f (g (diag f)) (λ n → sym (ap (λ x → x n) (fg (diag f))))
```

## Binary numbers

We use a modification of binary notation to avoid leading zeros and
hence multiple representations of the same number.

The isomorphic copy is formally constructed from 0 by iterating the
functions left(n)=2n+1 and right(n)=2n+2. This is illustrated by the
following tree:

```text
  ...   ...   ...  ...  ...  ...  ...   ...
   7     8     9    10  11   12    13   14
     \  /       \  /      \ /        \ /
      3           4        5          6
        \        /          \        /
            1                   2
              \                /

                       0
```
Define the above two functions:

```agda
left right : ℕ → ℕ
left  n = suc n + n
right n = suc (suc n) + n
```


Modified binary rendering of the natural numbers:

```agda
data 𝔹 : Type where
 Z : 𝔹
 L : 𝔹 → 𝔹
 R : 𝔹 → 𝔹
```

The successor function n ↦ n+1 on 𝔹:

```agda
Suc : 𝔹 → 𝔹
Suc Z = L Z
Suc (L b) = R b
Suc (R b) = L (Suc b)
```

Conversion between the two renderings:

```agda
unary : 𝔹 → ℕ
unary Z = 0
unary (L b) = left (unary b)
unary (R b) = right (unary b)

binary : ℕ → 𝔹
binary zero = Z
binary (suc n) = Suc (binary n)
```

HINT. Use the functions `left`, `right` and `Suc`.

Next we show that the functions binary and unary are mutually
inverse, after we formulate and prove some lemmas for that.

First some commutation properties:

```text
               left
          ℕ ─────────► ℕ
          │            │
   binary │            │ binary       (ldiagram)
          │            │
          ▼            ▼
          𝔹 ─────────► 𝔹
                L


               right
          ℕ ─────────► ℕ
          │            │
   binary │            │ binary       (rdiagram)
          │            │
          ▼            ▼
          𝔹 ─────────► 𝔹
                R


               Succ
          𝔹 ─────────► 𝔹
          │            │
    unary │            │ unary       (sdiagram)
          │            │
          ▼            ▼
          ℕ ─────────► ℕ
              succ
```


```agda
ldiagram : (n : ℕ) → binary (left n) ≡ L (binary n)
ldiagram zero = refl (L Z)
ldiagram (suc n) =
   Suc (Suc (binary (n + suc n))) ≡⟨ ap (Suc ∘ Suc) (
     binary (n + suc n) ≡⟨ ap binary (+-step n n) ⟩
     binary (suc n + n) ≡⟨ refl _ ⟩
     Suc (binary (n + n)) ∎)
   ⟩
   Suc (Suc (Suc (binary (n + n)))) ≡⟨ ap (Suc ∘ Suc) (ldiagram n) ⟩
   Suc (R (binary n)) ≡⟨ refl (L (Suc (binary n))) ⟩
   L (Suc (binary n)) ∎


rdiagram : (n : ℕ) → binary (right n) ≡ R (binary n)
rdiagram zero = refl (R Z)
rdiagram (suc n) =
   Suc (Suc (Suc (binary (n + suc n)))) ≡⟨
    ap
    (Suc ∘ (Suc ∘ Suc))
    (ap binary (+-step n n))
   ⟩
   Suc (Suc (Suc (Suc (binary (n + n))))) ≡⟨ ap (Suc ∘ Suc) (rdiagram n) ⟩
   R (Suc (binary n)) ∎

sdiagram : (m : 𝔹) → unary (Suc m) ≡ suc (unary m)
sdiagram Z = refl 1
sdiagram (L m) = refl (suc (suc (unary m + unary m)))
sdiagram (R m) = ap suc (
   unary (Suc m) + unary (Suc m) ≡⟨ ap (λ x → x + x) (sdiagram m) ⟩
   suc (unary m) + suc (unary m) ≡⟨ ap suc (+-step (unary m) (unary m)) ⟩
   suc (suc (unary m + unary m)) ∎
   )
```

The functions unary and binary are mutually inverse, using the above
diagrams:

```agda
unary-binary : (n : ℕ) → unary (binary n) ≡ n
unary-binary zero = refl zero
unary-binary (suc n) = 
   unary (Suc (binary n)) ≡⟨ sdiagram (binary n) ⟩
   suc (unary (binary n)) ≡⟨ ap suc (unary-binary n) ⟩
   suc n ∎

binary-unary : (m : 𝔹) → binary (unary m) ≡ m
binary-unary Z = refl Z
binary-unary (L m) = 
   Suc (binary (unary m + unary m)) ≡⟨ ldiagram (unary m) ⟩
   L (binary (unary m)) ≡⟨ ap L (binary-unary m) ⟩
   L m ∎
binary-unary (R m) = 
   Suc (Suc (binary (unary m + unary m))) ≡⟨ rdiagram (unary m) ⟩
   R (binary (unary m)) ≡⟨ ap R (binary-unary m) ⟩
   R m ∎
```

Example. We define a function height such that `height (2ⁿ-1) = n`.

The height of a number is its height in the following infinite tree:

```text
  ...   ...   ...  ...  ...  ...  ...   ...
   7     8     9    10  11   12    13   14
     \  /       \  /      \ /        \ /
      3           4        5          6
        \        /          \        /
            1                   2
              \                /

                       0
```

```agda
size : 𝔹 → ℕ
size Z     = 0
size (L m) = suc (size m)
size (R m) = suc (size m)

height : ℕ → ℕ
height n = size (binary n)

height-examples : (height 0  ≡ 0)
                × (height 1  ≡ 1)
                × (height 2  ≡ 1)
                × (height 3  ≡ 2)
                × (height 4  ≡ 2)
                × (height 5  ≡ 2)
                × (height 6  ≡ 2)
                × (height 7  ≡ 3)
                × (height 8  ≡ 3)
                × (height 9  ≡ 3)
                × (height 10 ≡ 3)
                × (height 11 ≡ 3)
                × (height 12 ≡ 3)
                × (height 13 ≡ 3)
                × (height 14 ≡ 3)
                × (height 15 ≡ 4)
                × (height 16 ≡ 4)
                × (height 17 ≡ 4)
height-examples = refl _ , refl _ , refl _ , refl _ , refl _ , refl _ , refl _ , refl _ , refl _ ,
                  refl _ , refl _ , refl _ , refl _ , refl _ , refl _ , refl _ , refl _ , refl _
```

The above diagrams give the following equations for the function height.

```agda
height-equation₀ : height 0 ≡ 0
height-equation₀ = refl zero

height-equation-l : (n : ℕ) → height (left n) ≡ suc (height n)
height-equation-l n = ap size (ldiagram n)


height-equation-r : (n : ℕ) → height (right n) ≡ suc (height n)
height-equation-r n = ap size (rdiagram n)

```

Now use these thre equations to show that height (2ⁿ-1) ≡ n.

```agda
power2 : ℕ → ℕ
power2 0       = 1
power2 (suc n) = double (power2 n)

height-power2-equation : (n : ℕ) → height (pred (power2 n)) ≡ n
height-power2-equation zero = height-equation₀
height-power2-equation (suc n) = {!n!}
```

This means that `height` computes an approximation of the logarithm function in base 2.

### Define addition of binary natural numbers

### Prove that it is correct

7 = 111 = left  left  left

4 = 100 =       right left
3 = 011 =       left  left

1 = 001 =             left

2 = 010 =             right

6 = 110 =       right right

```agda
_+𝔹_ : 𝔹 → 𝔹 → 𝔹
Z   +𝔹 m   = m
L n +𝔹 Z   = L n
L n +𝔹 L m = R (n +𝔹 m)
L n +𝔹 R m = L (Suc (n +𝔹 m))
R n +𝔹 Z   = R n
R n +𝔹 L m = L (Suc (n +𝔹 m))
R n +𝔹 R m = R (Suc (n +𝔹 m))

+order-lemma : (a b : ℕ) → (a + b) + a + b ≡ (a + a) + b + b
+order-lemma zero b = refl _
+order-lemma (suc a) b = ap suc (
   (a + b) + suc (a + b)   ≡⟨ +-step (a + b) (a + b) ⟩
   suc ((a + b) + (a + b)) ≡⟨ ap suc (+order-lemma a b) ⟩
   suc (a + a) + (b + b)   ≡⟨ ap (_+ b + b) (sym (+-step a a)) ⟩
   (a + suc a) + b + b     ∎
 )

+-step2 : (x y : ℕ) → x + suc (suc y) ≡ suc (suc (x + y))
+-step2 zero y = refl (suc (suc y))
+-step2 (suc zero) y = refl _
+-step2 (suc (suc x)) y = ap suc (ap suc (+-step2 x y))

lemma : (x y : ℕ) → x + x ≡ y + y → x ≡ y
lemma zero zero eq = refl zero
lemma (suc x) (suc y) eq = ap suc (lemma x y (ap pred II))
  where
    I : x + suc x ≡ y + suc y
    I = ap pred eq

    II : suc x + x ≡ suc y + y
    II = 
      suc x + x ≡⟨ +-comm (suc x) x ⟩
      x + suc x ≡⟨ I ⟩
      y + suc y ≡⟨ +-comm y (suc y) ⟩
      suc y + y ∎

ap-+ : (x y : ℕ)(f : ℕ → ℕ) → x + x ≡ y + y → f x + f x ≡ f y + f y
ap-+ x y f eq = ap (λ n → f n + f n) (lemma x y eq)

ap-+2 : (x y : ℕ)(f : ℕ → ℕ) → x ≡ y → f x + f x ≡ f y + f y
ap-+2 x y f eq = ap (λ n → f n + f n) eq

ap-+3 : (x y : ℕ) → x ≡ y → x + x ≡ y + y
ap-+3 x .x (refl .x) = refl _

suc-unary-lemma : (x : 𝔹) → unary (Suc x) ≡ suc (unary x)
suc-unary-lemma Z = refl 1
suc-unary-lemma (L x) = refl (suc (suc (unary x + unary x)))
suc-unary-lemma (R x) = ap suc (
   unary (Suc x) + unary (Suc x) ≡⟨ ap-+3 (unary (Suc x)) (suc (unary x)) (suc-unary-lemma x) ⟩
   suc (unary x) + suc (unary x) ≡⟨ ap suc (+-step (unary x) (unary x)) ⟩
   suc (suc (unary x + unary x)) ∎
 )

+𝔹-correct : (x y : 𝔹) → unary (x +𝔹 y) ≡ unary x + unary y
+𝔹-correct Z y = refl (unary y)
+𝔹-correct (L x) Z = +-comm zero (suc (unary x + unary x))
+𝔹-correct (L x) (L y) = ap suc (
   suc (unary (x +𝔹 y) + unary (x +𝔹 y))           ≡⟨ ap suc (ap (λ z → z + z) (+𝔹-correct x y)) ⟩
   suc ((unary x + unary y) + unary x + unary y)   ≡⟨ ap suc (+order-lemma (unary x) (unary y)) ⟩
   suc ((unary x + unary x) + (unary y + unary y)) ≡⟨ sym (+-step _ _) ⟩
   (unary x + unary x) + suc (unary y + unary y)   ∎
 )
+𝔹-correct (L x) (R y) = ap suc ( 
   unary (Suc (x +𝔹 y)) + unary (Suc (x +𝔹 y))   ≡⟨ ap-+3 (unary (Suc (x +𝔹 y))) (suc (unary (x +𝔹 y))) (suc-unary-lemma (x +𝔹 y)) ⟩
   suc (unary (x +𝔹 y)) + suc (unary (x +𝔹 y))   ≡⟨ ap suc (+-step (unary (x +𝔹 y)) (unary (x +𝔹 y))) ⟩
   suc (suc (unary (x +𝔹 y)) + (unary (x +𝔹 y))) ≡⟨ ap suc (ap suc (
       unary (x +𝔹 y) + unary (x +𝔹 y)         ≡⟨ ap-+3 (unary (x +𝔹 y)) (unary x + unary y) (+𝔹-correct x y) ⟩
       (unary x + unary y) + unary x + unary y ≡⟨ +order-lemma (unary x) (unary y) ⟩
       (unary x + unary x) + unary y + unary y ∎
   )) ⟩
   suc (suc ((unary x + unary x) + (unary y + unary y)))  ≡⟨ sym (+-step2 (unary x + unary x) (unary y + unary y)) ⟩
   (unary x + unary x) + suc (suc (unary y + unary y)) ∎
 )
+𝔹-correct (R x) Z = +-comm zero (suc (suc (unary x + unary x)))
+𝔹-correct (R x) (L y) = ap suc (
   unary (Suc (x +𝔹 y)) + unary (Suc (x +𝔹 y))           ≡⟨ ap-+3 (unary (Suc (x +𝔹 y))) (suc (unary (x +𝔹 y))) (suc-unary-lemma (x +𝔹 y)) ⟩
   suc (unary (x +𝔹 y)) + suc (unary (x +𝔹 y))           ≡⟨ ap suc (+-step (unary (x +𝔹 y)) (unary (x +𝔹 y))) ⟩
   suc (suc (unary (x +𝔹 y)) + (unary (x +𝔹 y)))         ≡⟨ ap suc (ap suc (
       unary (x +𝔹 y) + unary (x +𝔹 y)         ≡⟨ ap-+3 (unary (x +𝔹 y)) (unary x + unary y) (+𝔹-correct x y) ⟩
       (unary x + unary y) + unary x + unary y ≡⟨ +order-lemma (unary x) (unary y) ⟩
       (unary x + unary x) + unary y + unary y ∎
   )) ⟩
   suc (suc ((unary x + unary x) + (unary y + unary y))) ≡⟨ ap suc (sym (+-step (unary x + unary x) (unary y + unary y))) ⟩
   suc ((unary x + unary x) + suc (unary y + unary y))   ≡⟨ ap suc (ap ((unary x + unary x) +_) (ap suc (refl (unary y + unary y)))) ⟩
   suc ((unary x + unary x) + left (unary y)) ∎
 )
+𝔹-correct (R x) (R y) = ap suc (ap suc (
   unary (Suc (x +𝔹 y)) + unary (Suc (x +𝔹 y))           ≡⟨ ap-+3 (unary (Suc (x +𝔹 y))) (suc (unary (x +𝔹 y))) (suc-unary-lemma (x +𝔹 y)) ⟩
   suc (unary (x +𝔹 y)) + suc (unary (x +𝔹 y))           ≡⟨ ap suc (+-step (unary (x +𝔹 y)) (unary (x +𝔹 y))) ⟩
   suc (suc (unary (x +𝔹 y)) + (unary (x +𝔹 y)))         ≡⟨  ap suc (ap suc (
       unary (x +𝔹 y) + unary (x +𝔹 y)         ≡⟨ ap-+3 (unary (x +𝔹 y)) (unary x + unary y) (+𝔹-correct x y) ⟩
       (unary x + unary y) + unary x + unary y ≡⟨ +order-lemma (unary x) (unary y) ⟩
       (unary x + unary x) + unary y + unary y ∎
   )) ⟩
   suc (suc ((unary x + unary x) + (unary y + unary y))) ≡⟨ sym (+-step2 (unary x + unary x) (unary y + unary y)) ⟩
   (unary x + unary x) + suc (suc (unary y + unary y))   ≡⟨ ap ((unary x + unary x) +_) (refl _) ⟩
   (unary x + unary x) + right (unary y) ∎
 ))
```

# Challenging exercises on well-founded orders and sorting

```agda
open import strict-total-order
open import sorting
open import well-founded
```

In this set of exercises, we will practice using well-founded
recursion to define the beginning of the merge sort.

The central idea of the merge sort is the idea of "merging" two lists.
The process of merging can be described as follows: if either of the
lists is empty, then the merge is simply the other list.  If they are
both non-empty, we inspect the head and use `trichotomy` to decide
which is the smaller.  We keep the smaller of the two and now
recursively merge the tail of list from which we kept the smaller
element with the other list.

To make this idea into a sorting algorithm, we first write a function
to split a list into two, for example keeping the even-indexed elements
in the first list and the odd-indexed ones in the second.  Now we recursively
merge-sort these two sublists and merge the results.

Let tackle this idea of splitting first:

## Splitting by evens and odds

Write functions

```agda
evens : {X : Type} → List X → List X
odds : {X : Type} → List X → List X

evens [] = []
evens (x :: xs) = x :: odds xs
odds [] = []
odds (x :: []) = []
odds (x :: y :: xs) = evens (y :: xs)

_ : evens (1 :: 2 :: 3 :: []) ≡ 1 :: 3 :: []
_ = refl (1 :: 3 :: [])

_ : odds (1 :: 2 :: 3 :: []) ≡ 2 :: []
_ = refl (2 :: [])

_ : evens (0 :: 1 :: 2 :: 3 :: []) ≡ 0 :: 2 :: []
_ = refl (zero :: 2 :: [])

_ : odds (0 :: 1 :: 2 :: 3 :: []) ≡ 1 :: 3 :: []
_ = refl (1 :: 3 :: [])
```

which keep the even-indexed elements and odd-indexed elements respectively.

Note that by declaring the types first, before given the definitions,
Agda allows us to define these functions mutually recursively (that
is, the definition of `evens` may use `odds` and vice versa).  You may
wish to use this in your definition, though it is not necessary.

As an example, we should have
  * `evens (0 :: 1 :: 2 :: 3 :: []) = 0 :: 2 :: []`
  * `odds (0 :: 1 :: 2 :: 3 :: []) = 1 :: 3 :: []`

Later we will need to that when we apply these funtions to a list
with at least two elements, then the result is always shorter.  Let's
prove that now:

```agda

module _ {X : Type} where

  open <ₗ-wf X

  evens-shorter : (x y : X) (xs : List X) → evens (x :: y :: xs) <ₗ (x :: y :: xs)
  odds-shorter : (x y : X) (xs : List X) → odds (x :: y :: xs) <ₗ (x :: y :: xs)

  evens-shorter x y []        = <-suc <-zero
  evens-shorter x y (z :: xs) = <-suc (odds-shorter y z xs) 
  odds-shorter x y []        = <-suc <-zero
  odds-shorter x y (z :: xs) = <-suc (<ₙ-trans (<ₙ-lem (length (odds (z :: xs)))) (evens-shorter y z xs))
```

## Merging

Now let's implement the idea of merging two lists.  A naive attempt might look
as follows:

```agda
module _ {X : Type} (τ : StrictTotalOrder X) where
  open StrictTotalOrder τ

  -- merge-bad : List X × List X → List X
  -- merge-bad ([] , ys) = ys
  -- merge-bad (x :: xs , []) = x :: xs
  -- merge-bad (x :: xs , y :: ys) with trichotomy x y
  -- merge-bad (x :: xs , y :: ys) | inl x<y = x :: merge-bad (xs , y :: xs)
  -- merge-bad (x :: xs , y :: ys) | inr y≤x = y :: merge-bad (x :: xs , ys)
```

But if you uncomment this code, you will find that Agda cannot see that it
terminates.  Let's try to use well-founded induction to fix this (since we
can clearly see that in each recursive call **one** of the two lists does
indeed get shorter).

Since the argument to our function is a *pair* of lists, we first need
to extend our `_<ₗ_` relation to pairs.  This can be done using the
**lexicographic** ordering, which we define here for any pair of relations.

```agda
module Lex-wf
  {X : Type} {Y : Type}
  (_<[X]_ : X → X → Type)
  (_<[Y]_ : Y → Y → Type) where

  data _<[Lex]_ : X × Y → X × Y → Type where
    lex-left : {x₀ x₁ : X} {y₀ y₁ : Y} → x₀ <[X] x₁ → (x₀ , y₀) <[Lex] (x₁ , y₁)
    lex-right : {x₀ : X} {y₀ y₁ : Y} → y₀ <[Y] y₁ → (x₀ , y₀) <[Lex] (x₀ , y₁)
```

The key fact now is that if both of the relations are well-founded, so is their
lexicographic pairing:

```agda
  WF-Lex : WF _<[X]_ → WF _<[Y]_ → WF _<[Lex]_
  WF-Lex wfx wfy (x , y) = acc (lexAcc (wfx x) (wfy y))

    where lexAcc : ∀ {x y} → Acc _<[X]_ x → Acc _<[Y]_ y
            → (xy : X × Y) → xy <[Lex] (x , y) → Acc _<[Lex]_ xy
          lexAcc {x} {y} (acc ϕX) accy (x₀ , y₀) (lex-left x₀<x) = acc (lexAcc (ϕX x₀ x₀<x) (wfy y₀))
          lexAcc {x} {y} accx (acc ϕY) (x₀ , y₀) (lex-right y₀<y) = acc (lexAcc accx (ϕY y₀ y₀<y))
```

With these tools in hand, write a terminating version of the merge of two lists:

```agda
module _ (X : Type) (τ : StrictTotalOrder X) where

  open StrictTotalOrder τ
  open <ₗ-wf X
  open Lex-wf _<ₗ_ _<ₗ_

  wf-merge : List X × List X → List X
  wf-merge pxs = wf-ind _<[Lex]_ (λ _ → List X) (WF-Lex <ₗ-WF <ₗ-WF) goal pxs
    where
     goal : (x : List X × List X) → ((y : List X × List X) → y <[Lex] x → List X) → List X
     goal ([] , ys) mg-ih = ys
     goal (x :: xs , []) mg-ih = x :: xs
     goal (x :: xs , y :: ys) mg-ih with trichotomy x y
     goal (x :: xs , y :: ys) mg-ih | inl x<y = x :: mg-ih (xs , y :: ys) (lex-left (<ₙ-lem (length xs))) 
     goal (x :: xs , y :: ys) mg-ih | inr y≤x = y :: mg-ih (x :: xs , ys) (lex-right (<ₙ-lem (length ys)))
```

There are often other ways to rewrite a definition in an equivalent
way that Agda can indeed see terminates.  This is the case with the
merge function: we can split it into a pair of mutually defined
functions so that `merge-left` always consumes its left argument and
`merge-right` always consumes its right one (while keeping an
auxillary element in scope).  See if you can figure out how this works:

```agda
  merge-left : List X → List X → List X
  merge-right : X → List X → List X → List X

  merge-left [] ys = ys
  merge-left (x :: xs) [] = x :: xs
  merge-left (x :: xs) (y :: ys) with trichotomy x y
  merge-left (x :: xs) (y :: ys) | inl x<y = x :: merge-left xs (y :: ys)
  merge-left (x :: xs) (y :: ys) | inr y≤x = y :: merge-right x xs ys

  merge-right x xs [] = x :: xs
  merge-right x xs (y :: ys) with trichotomy x y
  merge-right x xs (y :: ys) | inl x<y = x :: merge-left xs (y :: ys)
  merge-right x xs (y :: ys) | inr y≤x = y :: merge-right x xs ys
```

## Merge Sort

The naive implementation of merge sort now looks like this:

```agda
  -- merge-sort-bad : List X → List X
  -- merge-sort-bad [] = []
  -- merge-sort-bad (x :: []) = x :: []
  -- merge-sort-bad (x :: y :: xs) =
  --   wf-merge (merge-sort-bad (evens (x :: y :: xs)) ,
  --             merge-sort-bad (odds (x :: y :: xs)))
```

Again you will see that Agda cannot see that this functions
terminates.  Rewrite it using well-founded recursion.

```agda
  merge-sort : List X → List X
  merge-sort = wf-ind _<ₗ_ (λ _ → List X) <ₗ-WF goal
   where
    goal : (x : List X) → ((y : List X) → y <ₗ x → List X) → List X
    goal [] merge-sort-ih = []
    goal (x :: []) merge-sort-ih = x :: []
    goal (x :: y :: xs) merge-sort-ih =
     wf-merge (
      (merge-sort-ih (evens (x :: y :: xs)) (evens-shorter x y xs)) ,
      (merge-sort-ih (odds (x :: y :: xs)) (odds-shorter x y xs))
      )
```

For well-founded recursion you need to first call `wf-ind` then it needs to be passed 5 arguments:

1. The order that shows that the recursive call is smaller. So if your list is geting shorter this would be _<₁_ as it is the order on lists not the order of the elements within the list
2. An argument that specifies the type of the well founded induction and generally this should be a lambda with an underscore for the first argument and it returns the type that is the same as the return type of the original function
3. This is a proof that the order given in the first argument is well founded
4. This should be written as a **SUB PROOF** with a name such as `goal` which actually specifies how the well founded recursion occurs and has the following type
`(x : X) → (∀ y → (y < x) → P y) → P x)`, where P is the proposition given in 2n. and < is the relation given in argument 1. This function has two arguments:
  1. An element of the same type as the original expression
  2. An argument which represents how all further recursive calls should be made with
  Then in the body of the function you should specify how the well founded infuction 
5. The argument you took in from the fundtion. Note if you don't take in an argument you don't need this argument to wf-ind

For more of a challenge, try to construct the rest of the sorting
algorithm.  You will probably want to follow the style of
[quick-sort](../quick-sort.lagda.md).

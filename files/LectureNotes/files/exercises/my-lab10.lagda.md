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
lift _<_ (inl x)     (inl y)     = x < y
lift _<_ (inr true)  (inl y)     = 𝟘
lift _<_ (inr false) (inl y)     = 𝟙
lift _<_ (inl x)     (inr true)  = 𝟙
lift _<_ (inr true)  (inr true)  = 𝟘
lift _<_ (inr false) (inr true)  = 𝟙
lift _<_ (inl x)     (inr false) = 𝟘
lift _<_ (inr true)  (inr false) = 𝟘
lift _<_ (inr false) (inr false) = 𝟘
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
  f = {!!}

  g : 𝟙 ∔ ℕ → ℕ
  g = {!!}

  gf : (g ∘ f) ∼ id
  gf = {!!}

  fg : (f ∘ g) ∼ id
  fg = {!!}

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
length-aux-lemma = {!!}
```

and use it to **conclude** that `length-tail-rec` is correct (in the sense that
it computes the same thing as `length`):

```agda
length-tail-rec-is-correct : {A : Type} (xs : List A) → length-tail-rec xs ≡ length xs
length-tail-rec-is-correct = {!!}
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
 map-of-non-decreasing-preserves-sorted f m []              nil-sorted       = {!!}
 map-of-non-decreasing-preserves-sorted f m (x :: [])       sing-sorted      = {!!}
 map-of-non-decreasing-preserves-sorted f m (x :: x' :: xs) (adj-sorted s t) = {!!}
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
diag s = {!!}
```

Now prove that this works:
```agda
diag-correct : (s : ℕ → (ℕ → Bool))
             → (n : ℕ) → ¬ (diag s ∼ s n)
diag-correct s n = {!!}
```

## Use it to prove the following impossibility result

Use the functions defined above, even if you did not finish them, to complete the
proof that there can be no isomorphism between `ℕ` and `ℕ → Bool`.

```agda
ℕ≃ℕ→Bool-is-impossible : ¬ (ℕ ≅ (ℕ → Bool))
ℕ≃ℕ→Bool-is-impossible = {!!}
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
height-equation-l zero = refl 1
height-equation-l (suc n) = {!!}


height-equation-r : (n : ℕ) → height (right n) ≡ suc (height n)
height-equation-r zero = refl 1
height-equation-r (suc n) = {!!}

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

```agda
_+𝔹_ : 𝔹 → 𝔹 → 𝔹
_+𝔹_ = {!!}

+𝔹-correct : (x y : 𝔹) → unary (x +𝔹 y) ≡ unary x + unary y
+𝔹-correct = {!!}
```

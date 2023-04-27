# Week 10 - Lab Sheet Solutions

```agda
{-# OPTIONS --without-K --safe #-}

module exercises.lab10-solutions where

open import prelude
open import negation
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

### Exercise 1.1

```agda
[Fin_]-suc-is-injective : (n : ℕ) (x y : Fin n)
                        → _≡_ {Fin _} (suc x) (suc y) -- suc x ≡ suc y
                        → x ≡ y
[Fin n ]-suc-is-injective x .x (refl (suc x)) = refl x

[Fin_]-decidable : (n : ℕ) → has-decidable-equality (Fin n)
[Fin suc _ ]-decidable zero    zero    = inl (refl zero)
[Fin suc _ ]-decidable zero    (suc _) = inr (λ ())
[Fin suc _ ]-decidable (suc _) zero    = inr (λ ())
[Fin suc n ]-decidable (suc x) (suc y) with [Fin n ]-decidable x y
... | inl  x≡y = inl (ap suc x≡y)
... | inr ¬x≡y = inr (¬x≡y ∘ [Fin n ]-suc-is-injective x y)
```

### Exercise 1.2

```agda

[Fin_]_<_ : (n : ℕ) → (x y : Fin n) → Type
[Fin suc n ] zero  < zero  = 𝟘
[Fin suc n ] zero  < suc _ = 𝟙
[Fin suc n ] suc _ < zero  = 𝟘
[Fin suc n ] suc x < suc y = [Fin n ] x < y

[Fin_]-irreflexive : (n : ℕ) → (x : Fin n) → ¬ ([Fin n ] x < x)
[Fin (suc n) ]-irreflexive (suc x) x<x = [Fin n ]-irreflexive x x<x

[Fin_]-transitive : (n : ℕ) → {x y z : Fin n}
                  → [Fin n ] x < y → [Fin n ] y < z → [Fin n ] x < z
[Fin suc n ]-transitive {zero } {suc y} {suc z} x<y y<z = ⋆
[Fin suc n ]-transitive {suc x} {suc y} {suc z} x<y y<z
 = [Fin n ]-transitive x<y y<z

[Fin_]-connected : (n : ℕ) → {x y : Fin n}
                 → ¬ (x ≡ y) → ([Fin n ] x < y) ∔ ([Fin n ] y < x)
[Fin suc _ ]-connected {zero } {zero } ¬x≡y = inl (¬x≡y (refl zero))
[Fin suc _ ]-connected {zero } {suc _} ¬x≡y = inl ⋆
[Fin suc _ ]-connected {suc _} {zero } ¬x≡y = inr ⋆
[Fin suc n ]-connected {suc x} {suc y} ¬x≡y
 = [Fin n ]-connected (λ x≡y → ¬x≡y (ap suc x≡y))

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

```agda
module _
        (fact : {X Y : Type} → 𝟙 ∔ X ≅ 𝟙 ∔ Y → X ≅ Y)
       where

 open _≅_
 open _IsPermutationOf_
```

### Exercise 2.1

```agda
 Pos-iso-same-length : {A : Type} (xs ys : List A)
                     → Pos xs ≅ Pos ys → length xs ≡ length ys
 Pos-iso-same-length {A} []        []        p = refl 0
 Pos-iso-same-length {A} []        (x :: ys) p = 𝟘-elim (inverse (inl ⋆))
  where
   open is-bijection (bijectivity p)
   recall : Pos ([] {A}) ≅ Pos (x :: ys)
   recall = p
 Pos-iso-same-length {A} (x :: xs) []        p = 𝟘-elim (bijection p (inl ⋆))
  where
   recall : Pos (x :: xs) ≅ Pos ([] {A})
   recall = p
 Pos-iso-same-length {A} (x :: xs) (y :: ys) p = ap suc IH
  where
   recall : Pos (x :: xs) ≅ Pos (y :: ys)
   recall = p
   IH : length xs ≡ length ys
   IH = Pos-iso-same-length xs ys (fact p)
```

### Exercise 2.2

```agda
 permutations-have-same-length : {A : Type} (xs ys : List A)
                               → xs IsPermutationOf ys → length xs ≡ length ys
 permutations-have-same-length xs ys p = Pos-iso-same-length xs ys (pos-iso p)
```

## Adding min and max to an order

```agda
has-min : {X : Type} → StrictTotalOrder X → Type
has-min {X = X} sto = Σ -∞ ꞉ X , ((x : X) → -∞ < x )
 where
  open StrictTotalOrder sto
```

```agda
has-max : {X : Type} → StrictTotalOrder X → Type
has-max {X = X} sto = Σ +∞ ꞉ X , (((x : X) → x < +∞))
 where
  open StrictTotalOrder sto
```

```agda
lift : {X : Type} → (_<_ : X → X → Type) → X ∔ Bool → X ∔ Bool → Type
lift _<_ (inr false) (inr false) = 𝟘
lift _<_ (inr true)  (inr true)  = 𝟘
lift _<_ (inl x)     (inr false) = 𝟘
lift _<_ (inl x)     (inr true)  = 𝟙
lift _<_ (inr false) y           = 𝟙
lift _<_ (inr true)  y           = 𝟘
lift _<_ (inl x)     (inl y)     = x < y
```

```agda
add-bounds : {X : Type} → StrictTotalOrder X → StrictTotalOrder (X ∔ Bool)
add-bounds {X} sto = record
                      { _<_         = _<↑_
                      ; decidable   = decidable↑
                      ; irreflexive = irreflexive↑
                      ; transitive  = λ {x} {y} {z} → transitive↑ {x} {y} {z}
                      ; connected   = connected↑
                      }
 where
  open StrictTotalOrder sto

  _<↑_ : X ∔ Bool → X ∔ Bool → Type
  _<↑_ = lift _<_

  decidable↑ : has-decidable-equality (X ∔ Bool)
  decidable↑ = +-has-decidable-equality sto decidable Bool-has-decidable-equality

  irreflexive↑ : (x : X ∔ Bool) → ¬ (x <↑ x)
  irreflexive↑ (inl x)     = irreflexive x
  irreflexive↑ (inr true)  = λ ()
  irreflexive↑ (inr false) = λ ()

  transitive↑ : {x y z : X ∔ Bool} → x <↑ y → y <↑ z → x <↑ z
  transitive↑ {x = inl x}     {inr true}  {inl z}     p  ()
  transitive↑ {x = inl x}     {inr false} {inl z}     () q
  transitive↑ {x = inr true}  {inr false} {_}         () q
  transitive↑ {x = inl x}     {inl  _}    {inr true}  p q   = ⋆
  transitive↑ {x = inl x}     {inr  _}    {inr true}  p q   = ⋆
  transitive↑ {x = inl x}     {inr true}  {inr false} p q   = q
  transitive↑ {x = inl x}     {inr false} {inr false} p q   = q
  transitive↑ {x = inr true}  {inr true}  {z}         p  q  = q
  transitive↑ {x = inr false} {_}         {inl x}     p q   = ⋆
  transitive↑ {x = inr false} {_}         {inr true}  p q   = ⋆
  transitive↑ {x = inr false} {inr true}  {inr false} p q   = q
  transitive↑ {x = inr false} {inr false} {inr false} p q   = q
  transitive↑ {x = inl x}     {inl y}     {inl z}     p q   = transitive p q

  connected↑ : {x y : X ∔ Bool} → ¬ (x ≡ y) → (x <↑ y) ∔ (y <↑ x)
  connected↑ {inl    x}  {inl     _} p = connected λ { (refl _) → p (refl (inl x)) }
  connected↑ {inl    x}  {inr  true} _ = inl ⋆
  connected↑ {inl    x}  {inr false} _ = inr ⋆
  connected↑ {inr true}  {inl     _} _ = inr ⋆
  connected↑ {inr false} {inl     _} _ = inl ⋆
  connected↑ {inr false} {inr true}  _ = inl ⋆
  connected↑ {inr true}  {inr false} _ = inr ⋆
  connected↑ {inr true}  {inr true}  p = 𝟘-elim (p (refl (inr true)))
  connected↑ {inr false} {inr false} p = 𝟘-elim (p (refl (inr false)))
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
length-aux-lemma []        k = refl k
length-aux-lemma (x :: xs) k =
 length-aux xs (suc k) ≡⟨ IH                   ⟩
 length xs + suc k     ≡⟨ +-step (length xs) k ⟩
 suc (length xs + k)   ≡⟨ refl _ ⟩
 suc (length xs) + k   ≡⟨ refl _ ⟩
 length (x :: xs) + k  ∎
  where
   IH : length-aux xs (suc k) ≡ length xs + suc k
   IH = length-aux-lemma xs (suc k)
```

and use it to **conclude** that `length-tail-rec` is correct (in the sense that
it computes the same thing as `length`):

```agda
length-tail-rec-is-correct : {A : Type} (xs : List A)
                           → length-tail-rec xs ≡ length xs
length-tail-rec-is-correct xs = length-tail-rec xs ≡⟨ refl _                ⟩
                                length-aux xs 0    ≡⟨ length-aux-lemma xs 0 ⟩
                                length xs + 0      ≡⟨ +-base (length xs)    ⟩
                                length xs          ∎
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
 map-of-non-decreasing-preserves-sorted f m []              nil-sorted       =
  nil-sorted
 map-of-non-decreasing-preserves-sorted f m (x :: [])       sing-sorted      =
  sing-sorted
 map-of-non-decreasing-preserves-sorted f m (x :: x' :: xs) (adj-sorted s (inl e)) =
  adj-sorted (map-of-non-decreasing-preserves-sorted f m (x' :: xs) s) (inl (ap f e))
 map-of-non-decreasing-preserves-sorted f m (x :: x' :: xs) (adj-sorted s (inr l)) =
  adj-sorted (map-of-non-decreasing-preserves-sorted f m (x' :: xs) s) (m x x' l)

 -- Alternatively using a cases lemma
 map-of-non-decreasing-preserves-sorted' : (f : X → Y) → is-non-decreasing f
                                        → (xs : List X) → Sorted σ xs
                                        → Sorted τ (map f xs)
 map-of-non-decreasing-preserves-sorted' f m []              nil-sorted       =
  nil-sorted
 map-of-non-decreasing-preserves-sorted' f m (x :: [])       sing-sorted      =
  sing-sorted
 map-of-non-decreasing-preserves-sorted' f m (x :: x' :: xs) (adj-sorted s t) = γ
  where
   γ : Sorted τ (map f (x :: x' :: xs))
   γ = adj-sorted IH k
    where
     IH : Sorted τ (map f (x' :: xs))
     IH = map-of-non-decreasing-preserves-sorted' f m (x' :: xs) s
     k : (f x' ≡ f x) ∔ (f x <[Y] f x')
     k = cases t
      where
       cases : (x' ≡ x) ∔ (x <[X] x') → (f x' ≡ f x) ∔ (f x <[Y] f x')
       cases (inl e) = inl (ap f e)
       cases (inr l) = m x x' l
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
diag s n = not (s n n)
```

Now prove that this works:
```agda
diag-correct : (s : ℕ → (ℕ → Bool))
             → (n : ℕ) → ¬ (diag s ∼ s n)
diag-correct s n h = lemma (s n n) (h n)
 where
  lemma : (b : Bool) → ¬ (not b ≡ b)
  lemma true  = false-is-not-true
  lemma false = true-is-not-false
```

## Use it to prove the following impossibility result

Use the functions defined above, even if you did not finish them, to complete the
proof that there can be no isomorphism between `ℕ` and `ℕ → Bool`.

```agda
ℕ≃ℕ→Bool-is-impossible : ¬ (ℕ ≅ (ℕ → Bool))
ℕ≃ℕ→Bool-is-impossible iso = diag-correct s k impossible
 where
  open _≅_ iso
  open is-bijection bijectivity
  s : (ℕ → (ℕ → Bool))
  s = bijection
  k : ℕ
  k = inverse (diag s)
  claim : s k ≡ diag s
  claim = s k                          ≡⟨ refl _     ⟩
          bijection (inverse (diag s)) ≡⟨ ε (diag s) ⟩
          diag s                       ∎
  impossible : diag s ∼ s k
  impossible n = ap (λ - → - n) (sym claim)
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
left 0        = 1
left (suc n) = suc (suc (left n))
right n       = suc (left n)
```


Modified binary rendering of the natural numbers:

```agda
data 𝔹 : Type where
 Z : 𝔹
 L : 𝔹 → 𝔹
 R : 𝔹 → 𝔹
```

The sucessor function n ↦ n+1 on 𝔹:

```agda
Suc : 𝔹 → 𝔹
Suc Z     = L Z
Suc (L m) = R m
Suc (R m) = L (Suc m)
```

Conversion between the two renderings:

```agda
unary : 𝔹 → ℕ
unary Z     = 0
unary (L m) = left (unary m)
unary (R m) = right (unary m)

binary : ℕ → 𝔹
binary 0        = Z
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


               Suc
          𝔹 ─────────► 𝔹
          │            │
    unary │            │ unary       (sdiagram)
          │            │
          ▼            ▼
          ℕ ─────────► ℕ
              suc
```


```agda
ldiagram : (n : ℕ) → binary (left n) ≡ L (binary n)
ldiagram 0       = refl _
ldiagram (suc n) = ap (Suc ∘ Suc) (ldiagram n)

rdiagram : (n : ℕ) → binary (right n) ≡ R (binary n)
rdiagram 0       = refl _
rdiagram (suc n) = ap (Suc ∘ Suc) (rdiagram n)

sdiagram : (m : 𝔹) → unary (Suc m) ≡ suc (unary m)
sdiagram Z     = refl _
sdiagram (L m) = refl _
sdiagram (R m) = ap left (sdiagram m)
```

The functions unary and binary are mutually inverse, using the above
diagrams:

```agda
unary-binary : (n : ℕ) → unary (binary n) ≡ n
unary-binary 0       = refl _
unary-binary (suc n) =
 unary (binary (suc n)) ≡⟨ sdiagram (binary n) ⟩
 suc (unary (binary n)) ≡⟨ ap suc (unary-binary n) ⟩
 suc n                  ∎

binary-unary : (m : 𝔹) → binary (unary m) ≡ m
binary-unary Z     = refl _
binary-unary (L m) =
 binary (unary (L m)) ≡⟨ ldiagram (unary m) ⟩
 L (binary (unary m)) ≡⟨ ap L (binary-unary m) ⟩
 L m                  ∎
binary-unary (R m) =
 binary (unary (R m)) ≡⟨ rdiagram (unary m) ⟩
 R (binary (unary m)) ≡⟨ ap R (binary-unary m) ⟩
 R m                  ∎
```

Example. We define a function height such that height (2ⁿ-1) = n.

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
height-equation₀ = refl _

height-equationₗ : (n : ℕ) → height (left n) ≡ suc (height n)
height-equationₗ n =
 height (left n)        ≡⟨ refl _ ⟩
 size (binary (left n)) ≡⟨ ap size (ldiagram n) ⟩
 size (L (binary n))    ≡⟨ refl _ ⟩
 suc (size (binary n)) ≡⟨ refl _ ⟩
 suc (height n)        ∎

height-equationᵣ : (n : ℕ) → height (right n) ≡ suc (height n)
height-equationᵣ n =
 height (right n)       ≡⟨ refl _ ⟩
 size (binary (right n))≡⟨ ap size (rdiagram n) ⟩
 size (R (binary n))    ≡⟨ refl _ ⟩
 suc (size (binary n)) ≡⟨ refl _ ⟩
 suc (height n)        ∎
```

Now use these three equations to show that height (2ⁿ-1) ≡ n.

```agda
power2 : ℕ → ℕ
power2 0       = 1
power2 (suc n) = double (power2 n)

height-power2-equation : (n : ℕ) → height (pred (power2 n)) ≡ n
height-power2-equation n = VI
 where
  powerl : ℕ → ℕ
  powerl 0        = 0
  powerl (suc n) = left (powerl n)

  I : (n : ℕ) → left (double n) ≡ suc (double (double n))
  I 0        = refl _
  I (suc n) = ap (λ x → suc (suc (suc (suc x)))) (I n)

  II : (n : ℕ) → left (power2 n) ≡ suc (power2 (suc n))
  II 0        = refl _
  II (suc n) = I (power2 n)

  III : (n : ℕ) → suc (powerl n) ≡ power2 n
  III 0        = refl _
  III (suc n) = suc-is-injective p
   where
    p = suc (suc (powerl (suc n))) ≡⟨ refl _ ⟩
        suc (suc (left (powerl n))) ≡⟨ refl _ ⟩
        left (suc (powerl n))        ≡⟨ ap left (III n) ⟩
        left (power2 n)               ≡⟨ II n ⟩
        suc (power2 (suc n))        ∎

  IV : (n : ℕ) → powerl n ≡ pred (power2 n)
  IV n = ap pred (III n)

  V : (n : ℕ) → height (powerl n) ≡ n
  V 0        = refl _
  V (suc n) =
   height (powerl (suc n)) ≡⟨ refl _ ⟩
   height (left (powerl n)) ≡⟨ height-equationₗ (powerl n) ⟩
   suc (height (powerl n)) ≡⟨ ap suc (V n) ⟩
   suc n                   ∎

  VI = height (pred (power2 n)) ≡⟨ ap height (sym (IV n)) ⟩
       height (powerl n)        ≡⟨ V n ⟩
       n                        ∎
```

This means that `height` computes an approximation of the logarithm function in base 2.

### Define addition of binary natural numbers

```agda
_+♭_ : 𝔹 → 𝔹 → 𝔹
Z   +♭ x    = x
L x +♭ Z  = L x
L x +♭ L y  = R (x +♭ y)
L x +♭ R y   = L (Suc (x +♭ y))
R x +♭ Z    = R x
R x +♭ L y    = L (Suc (x +♭ y))
R x +♭ R y    = R (Suc (x +♭ y))

+♭-lemma : ∀ m n → Suc (m +♭ n) ≡ Suc m +♭ n
+♭-lemma Z     Z     = refl _
+♭-lemma Z     (L n) = refl _
+♭-lemma Z     (R n) = refl _
+♭-lemma (L m) Z     = refl _
+♭-lemma (L m) (L n) = refl _
+♭-lemma (L m) (R n) = refl _
+♭-lemma (R m) Z     = refl _
+♭-lemma (R m) (L n) = ap R (+♭-lemma m n)
+♭-lemma (R m) (R n) = ap (λ - → L (Suc -)) (+♭-lemma m n)
```

### Prove that it is correct

```agda
+diagram : ∀ m n → binary (m + n) ≡ binary m +♭ binary n
+diagram 0 m       = refl _
+diagram (suc m) n  =
 binary (suc m + n)         ≡⟨ refl _ ⟩
 Suc (binary (m + n))       ≡⟨ ap Suc (+diagram m n) ⟩
 Suc (binary m +♭ binary n) ≡⟨ +♭-lemma (binary m) (binary n) ⟩
 Suc (binary m) +♭ binary n ≡⟨ refl _ ⟩
 binary (suc m) +♭ binary n ∎
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
odds (x :: xs) = evens xs
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

  evens-shorter x y [] = <-suc <-zero
  evens-shorter x y (z :: xs) = <-suc (odds-shorter y z xs)

  odds-shorter x y [] = <-suc <-zero
  odds-shorter x y (z :: xs) = <ₙ-trans (evens-shorter y z xs) (<ₙ-lem (suc (suc (length xs))))
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
  wf-merge = wf-ind _<[Lex]_ (λ _ → List X) (WF-Lex <ₗ-WF <ₗ-WF) go

    where go : (xy : List X × List X) → (mg-ih : (lr : List X × List X) → lr <[Lex] xy → List X) → List X
          go ([] , ys) mg-ih = ys
          go (x :: xs , []) mg-ih = x :: xs
          go (x :: xs , y :: ys) mg-ih with trichotomy x y
          go (x :: xs , y :: ys) mg-ih | inl x<y = x :: mg-ih (xs , y :: xs) (lex-left (<ₙ-lem (length xs)))
          go (x :: xs , y :: ys) mg-ih | inr y≤x = y :: mg-ih (x :: xs , ys) (lex-right (<ₙ-lem (length ys)))
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

  merge-left [] r = r
  merge-left (x :: l) [] = x :: l
  merge-left (x :: l) (y :: r) with trichotomy x y
  merge-left (x :: l) (y :: r) | inl x<y = x :: merge-left l (y :: r)
  merge-left (x :: l) (y :: r) | inr y≤x = y :: merge-right x l r

  merge-right x ls [] = x :: ls
  merge-right x ls (y :: rs) with trichotomy x y
  merge-right x ls (y :: rs) | inl x<y = x :: merge-left ls (y :: rs)
  merge-right x ls (y :: rs) | inr y≤x = y :: merge-right x ls rs
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
  merge-sort = wf-ind _<ₗ_ (λ _ → List X) <ₗ-WF go

    where go : (x : List X) → ((y : List X) → y <ₗ x → List X) → List X
          go [] merge-srt = []
          go (x :: []) merge-srt = x :: []
          go (x :: y :: xs) merge-srt =
            wf-merge (merge-srt (evens (x :: y :: xs)) (evens-shorter x y xs) ,
                      merge-srt (odds (x :: y :: xs)) (odds-shorter x y xs))

```

For more of a challenge, try to construct the rest of the sorting
algorithm.  You will probably want to follow the style of
[quick-sort](../quick-sort.lagda.md).

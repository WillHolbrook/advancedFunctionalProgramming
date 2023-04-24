# Week 9 - Homework Sheet

```agda
{-# OPTIONS --without-K --safe #-}

module exercises.my-homework9 where

open import prelude
open import natural-numbers-functions hiding (_≤_ )
open import List-functions
open import strict-total-order
open import sorting
open import decidability
open import exercises.lab9-solutions hiding (_≤_)
```

For all of the following questions we will work with a type `X` that
has decidable equality and a strict total order `_<_`.

```agda
module _
        {X : Type}
        (sto : StrictTotalOrder X)
       where

 open StrictTotalOrder sto
```

## Exercise 1

In the [lecture notes](../sorting.lagda.md) the type `Pos xs` was
introduced for every list `xs : List X`.

This is the type of positions in the list; for example, the type
`Pos (1 :: 2 :: [ 3 ])` has elements `inl ⋆`, `inr (inl ⋆)` and
`inr (inr (inl ⋆))`, representing the first, second and third elements
of the list, respectively.

Given any list `xs : List X`, there is a natural ordering of its
positions.

**Define** this strict total order.

```agda
 _<[Pos]_ : {X : Type} {xs : List X} → Pos xs → Pos xs → Type
 _<[Pos]_ {X} {x :: xs} pos1 (inl ⋆) = 𝟘
 _<[Pos]_ {X} {x :: xs} (inl ⋆) (inr pos2) = 𝟙
 _<[Pos]_ {X} {x :: xs} (inr pos1) (inr pos2) = pos1 <[Pos] pos2
```

## Exercise 2

We give some facts about the type `Y ∔ Z` for any types `Y` and `Z`:

 1. `inl y` does not equal `inr z` (for all `y : Y` and `z : Z`),
 1. `inr z` does not equal `inl y` (for all `y : Y` and `z : Z`),
 1. If `inl y₁ ≡ inl y₂` then `y₁ ≡ y₂` (for all `y₁,y₂ : Y`),
 1. If `inr z₁ ≡ inr z₂` then `z₁ ≡ z₂` (for all `z₁,z₂ : Z`).

```agda
 inl-is-not-inr : {Y Z : Type} {y : Y} {z : Z}
                → ¬ (inl {Y} {Z} y ≡ inr {Y} {Z} z)
 inl-is-not-inr ()

 inr-is-not-inl : {Y Z : Type} {y : Y} {z : Z}
                → ¬ (inr {Y} {Z} z ≡ inl {Y} {Z} y)
 inr-is-not-inl ()

 inl-lc : {Y Z : Type} {y₁ y₂ : Y}
        → inl {Y} {Z} y₁ ≡ inl {Y} {Z} y₂ → y₁ ≡ y₂
 inl-lc (refl _) = refl _

 inr-lc : {Y Z : Type} {z₁ z₂ : Z}
        → inr {Y} {Z} z₁ ≡ inr {Y} {Z} z₂ → z₁ ≡ z₂
 inr-lc (refl _) = refl _
```

Using the facts above, **prove** that if both `Y` and `Z` have
[decidable equality](../decidability.lagda.md), then so does `Y ∔ Z`.

```agda
 +-has-decidable-equality : {Y Z : Type}
                          → has-decidable-equality Y
                          → has-decidable-equality Z
                          → has-decidable-equality (Y ∔ Z)
 +-has-decidable-equality deceqy deceqz (inl y1) (inl y2) = I (deceqy y1 y2)
   where
     I : is-decidable (y1 ≡ y2) → is-decidable (inl y1 ≡ inl y2)
     I (inl (refl .y1)) = inl (refl _)
     I (inr ¬eq) = inr (λ inleq → ¬eq (inl-lc inleq))
 +-has-decidable-equality deceqy deceqz (inl y1) (inr z2) = inr inl-is-not-inr
 +-has-decidable-equality deceqy deceqz (inr z1) (inl y2) = inr inr-is-not-inl
 +-has-decidable-equality deceqy deceqz (inr z1) (inr z2) = I (deceqz z1 z2)
   where
     I : is-decidable (z1 ≡ z2) → is-decidable (inr z1 ≡ inr z2)
     I (inl (refl .z1)) = inl (refl _)
     I (inr ¬eq) = inr (λ inreq → ¬eq (inr-lc inreq))
```

## Exercise 3

`_<[Pos]_` defined in Exercise 1 must satisfy all the necessary
properties of a strict total order:
  * `Pos xs` has decidable equality,
  * `_<[Pos]_` is irreflexive,
  * `_<[Pos]_` is transitive,
  * `_<[Pos]_` is connected.

**Prove** that it does.

```agda
 𝟙-has-decidable-equality : has-decidable-equality 𝟙
 𝟙-has-decidable-equality ⋆ ⋆ = inl (refl ⋆)
 
 <[Pos]-decidable : {xs : List X} → has-decidable-equality (Pos xs)
 <[Pos]-decidable {x :: xs} pos1 pos2
   = +-has-decidable-equality
     𝟙-has-decidable-equality
     (<[Pos]-decidable {xs})
     pos1
     pos2

 <[Pos]-irreflexive : {xs : List X} → (x : Pos xs) → ¬ (x <[Pos] x)
 <[Pos]-irreflexive {x :: xs} (inl ⋆) ()
 <[Pos]-irreflexive {x :: xs} (inr pos) pos<pos
   = <[Pos]-irreflexive {xs} pos pos<pos

 <[Pos]-transitive : {xs : List X} → {n m o : Pos xs}
                   → n <[Pos] m → m <[Pos] o → n <[Pos] o
 <[Pos]-transitive {x :: xs} {inl ⋆} {inr m} {inr o} n<m m<o = ⋆
 <[Pos]-transitive {x :: xs} {inr n} {inr m} {inr o} n<m m<o
   = <[Pos]-transitive {xs} {n} {m} {o} n<m m<o
 
 <[Pos]-connected : {xs : List X} → {n m : Pos xs}
                  → ¬ (n ≡ m) → (n <[Pos] m) ∔ (m <[Pos] n)
 <[Pos]-connected {x :: xs} {inl ⋆} {inl ⋆} ¬n≡m = 𝟘-elim (¬n≡m (refl _))
 <[Pos]-connected {x :: xs} {inl ⋆} {inr m} ¬n≡m = inl ⋆
 <[Pos]-connected {x :: xs} {inr n} {inl ⋆} ¬n≡m = inr ⋆
 <[Pos]-connected {x :: xs} {inr n} {inr m} ¬n≡m
   = <[Pos]-connected {xs} {n} {m} (λ n≡m → ¬n≡m (ap inr n≡m))

 STO : (xs : List X) → StrictTotalOrder (Pos xs)
 STO xs = record
          { _<_         = _<[Pos]_
          ; decidable   = <[Pos]-decidable
          ; irreflexive = <[Pos]-irreflexive
          ; transitive  = <[Pos]-transitive {xs}
          ; connected   = <[Pos]-connected
          }
```

## Exercise 4

As you saw in [this week's lab sheet](lab9-solutions.lagda.md),
every strict total order `_<_` has an associated non-strict total
order `_≤_`, defined `x ≤ y = (y ≡ x) ∔ (x < y)`.

We use this fact to extract `_≤_` on `X` and `_≤[Pos}_` on `Pos xs`
given any list `xs : List X`.

```agda 
 nsto : NonStrictTotalOrder X
 nsto = non-strict-total-order-from-strict-total-order sto

 NSTO : (xs : List X) → NonStrictTotalOrder (Pos xs)
 NSTO xs = non-strict-total-order-from-strict-total-order (STO xs)

 _≤_ : X → X → Type
 _≤_ = NonStrictTotalOrder._≤_ nsto

 _≤[Pos]_ : {xs : List X} → Pos xs → Pos xs → Type
 _≤[Pos]_ {xs} = NonStrictTotalOrder._≤_ (NSTO xs)

 ≤-reflexive : (x : X) → x ≤ x
 ≤-reflexive = NonStrictTotalOrder.reflexive nsto

 ≤-transitive : {x y z : X} → x ≤ y → y ≤ z → x ≤ z
 ≤-transitive = NonStrictTotalOrder.transitive nsto
```

Given any types `X` and `Y` equipped with non-strict total orders
`_≤X_` and `_≤Y_` respectively, we define the notion of a *monotonic
function*.

A function `f : X → Y` is monotonic if as the arguments increase (or
stay the same), the value of the function at the argument also
increases (or stays the same).

```agda
 monotonic : {X Y : Type}
           → NonStrictTotalOrder X → NonStrictTotalOrder Y
           → (f : X → Y) → Type
 monotonic {X} {Y} nstox nstoy f = (x y : X) → x ≤X y → f x ≤Y f y
   where
     _≤X_ = NonStrictTotalOrder._≤_ nstox
     _≤Y_ = NonStrictTotalOrder._≤_ nstoy
```

The `Inhab : Pos xs → X` function
[from the lecture notes](../sorting.lagda.md) is a monotonic function
when `xs` is a Sorted list: i.e., as the position argument increases
(or stays the same), the inhabitant obtained from the list also
increases (or stays the same).

To state this mathematically, we want to prove that if `n ≤[Pos] m`
then `Inhab xs n ≤ Inhab xs m`.

First we will prove two small lemmas.

### Exercise 4.1

**Prove** that if a list `(x :: xs)` is sorted, then the list `xs` is
also sorted.

```agda
 tail-sorted : (x : X) (xs : List X)
             → Sorted sto (x :: xs)
             → Sorted sto       xs
 tail-sorted x [] sing-sorted = nil-sorted
 tail-sorted x (y :: xs) (adj-sorted srtdy::xs _) = srtdy::xs
```

### Exercise 4.2

**Prove** that if a list `(x :: y :: xs)` is sorted, then the list
`(x :: xs)` is also sorted.

```agda
 drop-one-sorted : (x y : X) (xs : List X)
                 → Sorted sto (x :: y :: xs)
                 → Sorted sto (x      :: xs)
 drop-one-sorted x y [] srtd = sing-sorted
 drop-one-sorted x y (z :: xs) (adj-sorted (adj-sorted srtd y≤z) x≤y)
   = adj-sorted srtd (≤-transitive x≤y y≤z)
```

### Exercise 4.3

**Prove** that, given a sorted list `xs`, `Inhab xs` is monotonic.

```agda
 Inhab-monotonic : (xs : List X) → Sorted sto xs
                   → monotonic (NSTO xs) nsto (Inhab xs)
 Inhab-monotonic (x :: xs) srtd n .n (inl (refl .n))
  = inl (refl _)
 Inhab-monotonic (x :: y :: xs) (adj-sorted srtd x≤y) (inl ⋆) (inr (inl ⋆)) (inr ⋆)
  = x≤y
 Inhab-monotonic (x :: y :: xs) (adj-sorted srtd x≤y) (inl ⋆) (inr (inr m)) (inr ⋆)
  = Inhab-monotonic (x :: xs) (drop-one-sorted x y xs (adj-sorted srtd x≤y)) (inl ⋆) (inr m) (inr ⋆)
 Inhab-monotonic (x :: y :: xs) (adj-sorted srtd x≤y) (inr n) (inr m) (inr n<m)
  = Inhab-monotonic (y :: xs) (tail-sorted x (y :: xs) (adj-sorted srtd x≤y)) n m (inr n<m)
```

# Week 9 - Lab Sheet

```agda
{-# OPTIONS --safe --without-K --auto-inline #-}

module exercises.my-lab9v2 where

open import prelude
open import decidability
open import Fin
open import List-functions
open import isomorphisms
open import sorting
open import strict-total-order
```

In this lab sheet you will practice with **positions** in a list and **strict
total orders**.

## Exercise 1

Recall from the lectures that we defined a type of *positions* (or indices) for
a given list as follows.

```agdacode
Pos : {X : Type} → List X → Type
Pos        [] = 𝟘
Pos (_ :: xs) = 𝟙 ∔ Pos xs
```

We will consider an inductively defined version of here and prove it to be
isomorphic to `Pos`.

The inductive definition is as follows.

```agda
data Pos' {X : Type} : List X → Type where
  here : {x : X} {xs : List X}
       → Pos' (x :: xs)
  there : {x : X} {xs : List X}
        → (p : Pos' xs) → Pos' (x :: xs)
```

### Exercise 1.1

**Define** a function from `Pos xs` to `Pos' xs`.

```agda
Pos-to-Pos' : {X : Type} (xs : List X) → Pos xs → Pos' xs
Pos-to-Pos' (x :: xs) (inl ⋆) = here
Pos-to-Pos' (x :: xs) (inr pos) = there (Pos-to-Pos' xs pos)
```

### Exercise 1.2

**Define** a function the other way, i.e. from `Pos' xs` to `Pos xs`.

```agda
Pos'-to-Pos : {X : Type} (xs : List X) → Pos' xs → Pos xs
Pos'-to-Pos (x :: xs) here = inl ⋆
Pos'-to-Pos (x :: xs) (there pos) = inr (Pos'-to-Pos xs pos)
```

### Exercise 1.3

Using the above functions, **prove** that `Pos xs` is isomorphic to `Pos' xs`
for every list `xs`.

```agda
Pos-isomorphic-to-Pos' : {X : Type} (xs : List X) → Pos xs ≅ Pos' xs
Pos-isomorphic-to-Pos' {X} xs = record { bijection = f xs ; bijectivity = f-is-bijection }
 where
  f : (xs : List X) → Pos xs → Pos' xs
  f xs = Pos-to-Pos' xs

  g : (xs : List X) → Pos' xs → Pos xs
  g xs = Pos'-to-Pos xs

  gf : (xs : List X) → g xs ∘ f xs ∼ id
  gf (x :: xs) (inl ⋆)   = refl (inl ⋆)
  gf (x :: xs) (inr pos) = ap inr (gf xs pos)

  fg : (xs : List X) → f xs ∘ g xs ∼ id
  fg (x :: xs) here = refl here
  fg (x :: xs) (there pos) = ap there (fg xs pos)

  f-is-bijection : is-bijection (f xs)
  f-is-bijection = record { inverse = g xs ; η = gf xs ; ε = fg xs }

```

## Exercise 2

Yet another way to define the positions is by using `Fin (length xs)`, the
inductively defined type that has exactly `length xs`-many elements.

### Exercise 2.1

**Define** the map that takes a position of `xs` and gives an element of `Fin
  (length xs)`.

```agda
Pos-to-Fin-length : {X : Type} (xs : List X) → Pos xs → Fin (length xs)
Pos-to-Fin-length (x :: xs) (inl ⋆) = zero
Pos-to-Fin-length (x :: xs) (inr pos) = suc (Pos-to-Fin-length xs pos)
```

### Exercise 2.2

**Define** the map in the other direction.

```agda
Fin-length-to-Pos : {X : Type} (xs : List X) → Fin (length xs) → Pos xs
Fin-length-to-Pos (x :: xs) zero = inl ⋆
Fin-length-to-Pos (x :: xs) (suc fin) = inr (Fin-length-to-Pos xs fin)
```

### Exercise 2.3

Using the above functions, **prove** that `Pos xs` is isomorphic to `Fin (length
xs)` for every list `xs`.

```agda
Pos-isomorphic-to-Fin-length : {X : Type} (xs : List X)
                             → Pos xs ≅ Fin (length xs)
Pos-isomorphic-to-Fin-length {X} xs = record { bijection = f xs ; bijectivity = f-is-bijection }
 where
  f : (xs : List X) → Pos xs → Fin (length xs)
  f = Pos-to-Fin-length

  g : (xs : List X) → Fin (length xs) → Pos xs
  g = Fin-length-to-Pos

  gf : (xs : List X) → g xs ∘ f xs ∼ id
  gf (x :: xs) (inl ⋆)   = refl (inl ⋆)
  gf (x :: xs) (inr pos) = ap inr (gf xs pos)

  fg : (xs : List X) → f xs ∘ g xs ∼ id
  fg (x :: xs) zero = refl zero
  fg (x :: xs) (suc fin) = ap suc (fg xs fin)

  f-is-bijection : is-bijection (f xs)
  f-is-bijection = record { inverse = g xs ; η = gf xs ; ε = fg xs }

```

## Exercise 3

**Prove** that if `X` and `Y` have decidable equality, then so does their
cartesian product `X × Y`.

```agda
×-has-decidable-equality : {X Y : Type}
                         → has-decidable-equality X
                         → has-decidable-equality Y
                         → has-decidable-equality (X × Y)
×-has-decidable-equality deceqx deceqy (x1 , y1) (x2 , y2) with deceqx x1 x2 | deceqy y1 y2
×-has-decidable-equality deceqx deceqy (x1 , y1) (x2 , y2) | inl x1=x2 | inr ¬y1=y2
 = inr (λ {(refl .(x1 , y1)) → ¬y1=y2 (refl y1)})
×-has-decidable-equality deceqx deceqy (x1 , y1) (x1 , .y1) | inl (refl .x1) | inl (refl .y1)
 = inl (refl (x1 , y1))
×-has-decidable-equality deceqx deceqy (x1 , y1) (x2 , y2) | inr ¬x1=x2 | _
 = inr λ {(refl .(x1 , y1)) → ¬x1=x2 (refl x1)}
```

**Conclude** that `ℕ × ℕ` has decidable equality.

```agda
ℕ² : Type
ℕ² = ℕ × ℕ

ℕ²-has-decidable-equality : has-decidable-equality ℕ²
ℕ²-has-decidable-equality = ×-has-decidable-equality ℕ-has-decidable-equality ℕ-has-decidable-equality
```

## Exercise 4

The *lexicographical order* on `ℕ²` is defined as: `(n , m) < (n' , m')`
precisely when (`n < n'`) or (`n = n'` and `m < m'`).

So, for example, `(3 , 19) < (5, 2)` and `(7 , 3) < (7 , 4)`, but `¬ (11 , 4) <
(11 , 1)` and `¬ (5 , 1) < (4 , 3)`.

We are going to prove that the lexicographical order is a strict total order on
`ℕ²`.

### Exercise 4.1

**Translate** the definition of the lexicographical order to Agda.

```agda
_<ₗ_ : ℕ² → ℕ² → Type
(n , m) <ₗ (n' , m') = (n <ₙ n') ∔ ((n ≡ n') × (m <ₙ m')) 
```

### Exercise 4.2

**Prove** that the lexicographical order is irreflexive.

```agda
<ₗ-is-irreflexive : (p : ℕ²) → ¬ (p <ₗ p)
<ₗ-is-irreflexive (n , m) (inl n<n) = <ₙ-irreflexive n n<n
<ₗ-is-irreflexive (n , m) (inr (n=n , m<m)) = <ₙ-irreflexive m m<m
```

### Exercise 4.3

**Prove** that the lexicographical order is transitive.

```agda
<ₗ-is-transitive : {p q r : ℕ²} → p <ₗ q → q <ₗ r → p <ₗ r
<ₗ-is-transitive {n , m} {n' , m'} {n'' , m''} (inl n<n') (inl n'<n'')
 = inl (<ₙ-trans n<n' n'<n'')
<ₗ-is-transitive {n , m} {n' , m'} {.n' , m''} (inl n<n') (inr (refl .n' , m'<m''))
 = inl n<n'
<ₗ-is-transitive {n , m} {.n , m'} {n'' , m''} (inr (refl .n , m<m')) (inl n<n'')
 = inl n<n''
<ₗ-is-transitive {n , m} {.n , m'} {.n , m''} (inr (refl .n , m<m')) (inr (refl .n , m'<m''))
 = inr ((refl n) , (<ₙ-trans m<m' m'<m''))
```

### Exercise 4.4

**Prove** that the lexicographical is connected.

```agda
<ₗ-is-connected : {p q : ℕ²} → ¬ (p ≡ q) → (p <ₗ q) ∔ (q <ₗ p)
<ₗ-is-connected {n , m} {n' , m'} ¬p=q with tri n n'
  where
    tri : (x y : ℕ) → (x <ₙ y) ∔ (x ≡ y) ∔ (y <ₙ x)
    tri = StrictTotalOrder.trichotomy ℕ-StrictTotalOrder
<ₗ-is-connected {n , m} {n' , m'} ¬p=q | inl n<n' = inl (inl n<n')
<ₗ-is-connected {n , m} {n' , m'} ¬p=q | inr (inl n=n') with tri m m'
  where
    tri : (x y : ℕ) → (x <ₙ y) ∔ (x ≡ y) ∔ (y <ₙ x)
    tri = StrictTotalOrder.trichotomy ℕ-StrictTotalOrder
<ₗ-is-connected {n , m} {n' , m'} ¬p=q | inr (inl n=n') | inl m<m' = inl (inr (n=n' , m<m'))
<ₗ-is-connected {n , m} {n , .m } ¬p=q | inr (inl (refl .n)) | inr (inl (refl .m))
 = 𝟘-elim (¬p=q (refl (n , m)))
<ₗ-is-connected {n , m} {n' , m'} ¬p=q | inr (inl n=n') | inr (inr m'<m)
 = inr (inr ((sym n=n') , m'<m))
<ₗ-is-connected {n , m} {n' , m'} ¬p=q | inr (inr n'<n) = inr (inl n'<n)
```

### Exercise 4.5

**Conclude** that the lexicographical order is a strict total order on `ℕ²`.

```agda
strict-total-order-on-ℕ² : StrictTotalOrder ℕ²
strict-total-order-on-ℕ² = record
                             { _<_ = _<ₗ_
                             ; irreflexive = <ₗ-is-irreflexive
                             ; transitive = <ₗ-is-transitive
                             ; connected = <ₗ-is-connected
                             ; decidable = ℕ²-has-decidable-equality
                             }
```

## Exercise 5

In the lectures, a type f strict total order was introduced. Similarly, we can
also introduce a type of *non-strict total orders*.

For example, the type of natural numbers with `≤` is an example of a non-strict
total order.

```agda
record NonStrictTotalOrder (X : Type) : Type₁ where
 field
  _≤_ : X → X → Type
  decidable : has-decidable-equality X
  reflexive : (x : X) → x ≤ x
  transitive : {x y z : X} → x ≤ y → y ≤ z → x ≤ z
  antisymmetric : {x y : X} → x ≤ y → y ≤ x → x ≡ y
  strongly-connected : (x y : X) → (x ≤ y) ∔ (y ≤ x)
```

Now let's assume that we are given a *strict* total order. We make this
assumption using a module, which means it will be available to you in the code
below.

```agda
module _
        {X : Type}
        (sto : StrictTotalOrder X)
       where
       
 open StrictTotalOrder sto
```

We can define the order `≤` from the strict total order `<` on `X` as follows.

```agda
 _≤_ : X → X → Type
 x ≤ y = (y ≡ x) ∔ (x < y)
```

Notice how `≤` was (implicitly) used in the definition of `Sorted` given in
[strict-total-order.lagda.md](../strict-total-order.lagda.md#sorted-lists).

### Exercise 5.1

**Prove** the following facts about `≤`.

```agda
 <-to-≤ : {x y : X} → x < y → x ≤ y
 <-to-≤ x<y = inr x<y

 ≤-is-reflexive : (x : X) → x ≤ x
 ≤-is-reflexive x = inl (refl x)
```

### Exercise 5.2

Using transitivity of `<`, **prove** a lemma and that `≤` is transitive.

```agda
 <-≤-trans : {x y z : X} → x < y → y ≤ z → x ≤ z
 <-≤-trans x<y (inl (refl _)) = inr x<y
 <-≤-trans x<y (inr y<z     ) = inr (transitive x<y y<z)

 ≤-is-transitive : {x y z : X} → x ≤ y → y ≤ z → x ≤ z
 ≤-is-transitive (inl (refl _)) y≤z = y≤z
 ≤-is-transitive (inr x<y) y≤z = <-≤-trans x<y y≤z
```

### Exercise 5.3

**Prove** antisymmetry of `≤`.

```agda
 ≤-is-antisymmetric : {x y : X} → x ≤ y → y ≤ x → x ≡ y
 ≤-is-antisymmetric (inl (refl _)) y≤x = refl _
 ≤-is-antisymmetric (inr x<y) (inl (refl _)) = refl _
 ≤-is-antisymmetric {x} {y} (inr x<y) (inr y<x) = 𝟘-elim (antisymmetric x y x<y y<x)
```

### Exercise 5.4

**Show** that `≤` is strongly connected.

```agda
 ≤-is-strongly-connected : (x y : X) → (x ≤ y) ∔ (y ≤ x)
 ≤-is-strongly-connected x y with trichotomy x y
 ≤-is-strongly-connected x y | inl x<y = inl (inr x<y)
 ≤-is-strongly-connected x y | inr (inl y=x) = inr (inl y=x)
 ≤-is-strongly-connected x y | inr (inr y<x) = inr (inr y<x)
```

### Exercise 5.5

Finally, **complete** the definition of the non-strict total order on `X`.

```agda
 non-strict-total-order-from-strict-total-order : NonStrictTotalOrder X
 non-strict-total-order-from-strict-total-order = record
   { _≤_ = _≤_
   ; decidable = decidable
   ; reflexive = ≤-is-reflexive
   ; transitive = ≤-is-transitive
   ; antisymmetric = ≤-is-antisymmetric
   ; strongly-connected = ≤-is-strongly-connected
   }
```

## Insertion Sort Exercises

Now study and complete the holes from [Tuesday's lecture sheet](/files/LectureNotes/files/insertion-sort-lecture.lagda.md).
Chiefly, you should prove that insertion sort is a sorting algorithm.

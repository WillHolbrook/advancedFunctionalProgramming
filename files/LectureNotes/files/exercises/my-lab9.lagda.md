# Week 9 - Lab Sheet

```agda
{-# OPTIONS  --allow-unsolved-metas --without-K --auto-inline #-}

module exercises.my-lab9 where

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
Pos-to-Pos' (x :: [])      (inl ⋆)     = here
Pos-to-Pos' (x :: y :: xs) (inl ⋆)     = here
Pos-to-Pos' (x :: y :: xs) (inr posxs) = there (Pos-to-Pos' (y :: xs) posxs)
```

### Exercise 1.2

**Define** a function the other way, i.e. from `Pos' xs` to `Pos xs`.

```agda
Pos'-to-Pos : {X : Type} (xs : List X) → Pos' xs → Pos xs
Pos'-to-Pos (x :: xs) here          = inl ⋆
Pos'-to-Pos (x :: xs) (there posxs) = inr (Pos'-to-Pos xs posxs)
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

  gf : (xs : List X) → g xs ∘ f xs  ∼ id
  gf (x :: [])      (inl ⋆)     = refl (inl ⋆)
  gf (x :: y :: xs) (inl ⋆)     = refl (inl ⋆)
  gf (x :: y :: xs) (inr posxs) = ap inr (gf (y :: xs) posxs)

  fg :  (xs : List X) → f xs ∘ g xs ∼ id
  fg (x :: [])      here          = refl here
  fg (x :: y :: xs) here          = refl here
  fg (x :: y :: xs) (there posxs) = ap there (fg (y :: xs) posxs)

  f-is-bijection : is-bijection (f xs)
  f-is-bijection = record { inverse = g xs ; η = gf xs; ε = fg xs }

```

## Exercise 2

Yet another way to define the positions is by using `Fin (length xs)`, the
inductively defined type that has exactly `length xs`-many elements.

### Exercise 2.1

**Define** the map that takes a position of `xs` and gives an element of `Fin
  (length xs)`.

```agda
Pos-to-Fin-length : {X : Type} (xs : List X) → Pos xs → Fin (length xs)
Pos-to-Fin-length (x :: [])      (inl ⋆)     = zero
Pos-to-Fin-length (x :: y :: xs) (inl ⋆)     = zero
Pos-to-Fin-length (x :: y :: xs) (inr posxs) = suc (Pos-to-Fin-length (y :: xs) posxs)
```

### Exercise 2.2

**Define** the map in the other direction.

```agda
Fin-length-to-Pos : {X : Type} (xs : List X) → Fin (length xs) → Pos xs
Fin-length-to-Pos (x :: [])      zero        = inl ⋆
Fin-length-to-Pos (x :: y :: xs) zero        = inl ⋆
Fin-length-to-Pos (x :: y :: xs) (suc finxs) = inr (Fin-length-to-Pos (y :: xs) finxs)
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
  gf (x :: [])      (inl ⋆)     = refl (inl ⋆)
  gf (x :: y :: xs) (inl ⋆)     = refl (inl ⋆)
  gf (x :: y :: xs) (inr posxs) = ap inr (gf (y :: xs) posxs)

  fg : (xs : List X) → f xs ∘ g xs ∼ id
  fg (x :: [])      zero        = refl zero
  fg (x :: y :: xs) zero        = refl zero
  fg (x :: y :: xs) (suc finxs) = ap suc (fg (y :: xs) finxs)

  f-is-bijection : is-bijection (f xs)
  f-is-bijection = record { inverse = g xs ; η = gf xs ; ε = fg xs }

```

## Exercise 3

**Prove** that if `X` and `Y` have decidable equality, then so does their
cartesian product `X × Y`.

```agda
flip : {X Y : Type} → X × Y → Y × X
flip (x , y) = y , x

pair-lemma1 : {X Y : Type}(x₁ x₂ : X)(y₁ y₂ : Y) → ¬ (x₁ ≡ x₂) → ¬ ((x₁ , y₁) ≡ (x₂ , y₂))
pair-lemma1 x₁ x₂ y₁ y₂ ¬eq eqpair = 𝟘-elim (¬eq (ap fst eqpair))

pair-lemma2 : {X Y : Type}(x₁ x₂ : X)(y₁ y₂ : Y) → ¬ (y₁ ≡ y₂) → ¬ ((x₁ , y₁) ≡ (x₂ , y₂))
pair-lemma2 x₁ x₂ y₁ y₂ ¬eq eqpair = 𝟘-elim (¬eq (ap snd eqpair))

pair-lemma3 : {X Y : Type}(x₁ x₂ : X)(y₁ y₂ : Y) → x₁ ≡ x₂ → y₁ ≡ y₂ → (x₁ , y₁) ≡ (x₂ , y₂)
pair-lemma3 x .x y .y (refl .x) (refl .y) = refl (x , y)

×-has-decidable-equality : {X Y : Type}
                         → has-decidable-equality X
                         → has-decidable-equality Y
                         → has-decidable-equality (X × Y)
×-has-decidable-equality deceqx deceqy (x₁ , y₁) (x₂ , y₂) = I (deceqx x₁ x₂) (deceqy y₁ y₂)
  where
    I : is-decidable (x₁ ≡ x₂) → is-decidable (y₁ ≡ y₂) → is-decidable ((x₁ , y₁) ≡ (x₂ , y₂))
    I (inl eqx)  (inl eqy)  = inl (pair-lemma3 x₁ x₂ y₁ y₂ eqx eqy)
    I (inl eqx)  (inr ¬eqy) = inr (pair-lemma2 x₁ x₂ y₁ y₂ ¬eqy)
    I (inr ¬eqx) _          = inr (pair-lemma1 x₁ x₂ y₁ y₂ ¬eqx)
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
(zero , m)     <ₗ (zero , zero)     = 𝟘
(zero , zero)  <ₗ (zero , suc m')   = 𝟙
(zero , suc m) <ₗ (zero , suc m')   = (zero , m) <ₗ (zero , m')
(zero , m)     <ₗ (suc n' , m')     = 𝟙
(suc n , m)    <ₗ (zero , m')       = 𝟘
(suc n , m)    <ₗ (suc n' , m')     = (n , m) <ₗ (n' , m')
```

### Exercise 4.2

**Prove** that the lexicographical order is irreflexive.

```agda
<ₗ-is-irreflexive : (p : ℕ²) → ¬ (p <ₗ p)
<ₗ-is-irreflexive (zero , suc m) p< = <ₗ-is-irreflexive (zero , m) p<
<ₗ-is-irreflexive (suc n , m) p< = <ₗ-is-irreflexive (n , m) p<
```

### Exercise 4.3

**Prove** that the lexicographical order is transitive.

```agda
<ₗ-is-transitive : {p q r : ℕ²} → p <ₗ q → q <ₗ r → p <ₗ r
<ₗ-is-transitive {zero , zero}     {zero , suc snd₂} {zero , suc snd₃} p<q q<r = ⋆
<ₗ-is-transitive {zero , zero}     {zero , suc snd₂} {suc fst₃ , snd₃} p<q q<r = ⋆
<ₗ-is-transitive {zero , suc snd₁} {zero , suc snd₂} {zero , suc snd₃} p<q q<r = <ₗ-is-transitive {zero , snd₁} {zero , snd₂} {zero , snd₃} p<q q<r
<ₗ-is-transitive {zero , suc snd₁} {zero , suc snd₂} {suc fst₃ , snd₃} p<q q<r = ⋆
<ₗ-is-transitive {zero , zero} {suc fst₁ , zero} {suc fst₂ , snd₁} p<q q<r = ⋆
<ₗ-is-transitive {zero , zero} {suc fst₁ , suc snd₁} {suc fst₂ , snd₂} p<q q<r = ⋆
<ₗ-is-transitive {zero , suc snd₁} {suc fst₁ , zero} {suc fst₂ , snd₂} p<q q<r = ⋆
<ₗ-is-transitive {zero , suc snd₁} {suc fst₁ , suc snd₂} {suc fst₂ , snd₃} p<q q<r = ⋆
<ₗ-is-transitive {suc fst₁ , snd₁} {zero , snd₂}     {zero , snd₃}     p<q q<r = p<q
<ₗ-is-transitive {suc fst₁ , snd₁} {suc fst₂ , snd₂} {zero , snd₃}     p<q q<r = q<r
<ₗ-is-transitive {suc fst₁ , snd₁} {suc fst₂ , snd₂} {suc fst₃ , snd₃} p<q q<r = <ₗ-is-transitive {fst₁ , snd₁} {fst₂ , snd₂} {fst₃ , snd₃} p<q q<r
```

### Exercise 4.4

**Prove** that the lexicographical is connected.

```agda
<ₗ-is-connected : {p q : ℕ²} → ¬ (p ≡ q) → (p <ₗ q) ∔ (q <ₗ p)
<ₗ-is-connected {zero , zero} {zero , zero} ¬peqq = 𝟘-elim (¬peqq (refl (zero , zero)))
<ₗ-is-connected {zero , zero} {zero , suc snd₂} ¬peqq = inl ⋆
<ₗ-is-connected {zero , suc snd₁} {zero , zero} ¬peqq = inr ⋆
<ₗ-is-connected {zero , suc snd₁} {zero , suc snd₂} ¬peqq = <ₗ-is-connected {zero , snd₁} {zero , snd₂} (λ prf → ¬peqq (ap (λ x → zero , suc (snd x)) prf))
<ₗ-is-connected {zero , zero} {suc fst₁ , zero} x = inl ⋆
<ₗ-is-connected {zero , zero} {suc fst₁ , suc snd₁} x = inl ⋆
<ₗ-is-connected {zero , suc snd₁} {suc fst₁ , zero} x = inl ⋆
<ₗ-is-connected {zero , suc snd₁} {suc fst₁ , suc snd₂} x = inl ⋆
<ₗ-is-connected {suc fst₁ , snd₁} {zero , zero} ¬peqq = inr ⋆
<ₗ-is-connected {suc fst₁ , snd₁} {zero , suc snd₂} ¬peqq = inr ⋆
<ₗ-is-connected {suc fst₁ , snd₁} {suc fst₂ , snd₂} ¬peqq = <ₗ-is-connected {fst₁ , snd₁} {fst₂ , snd₂} (λ prf → ¬peqq (ap (λ p → suc (fst p) , snd p) prf))
```

### Exercise 4.5

**Conclude** that the lexicographical order is a strict total order on `ℕ²`.

```agda
strict-total-order-on-ℕ² : StrictTotalOrder ℕ²
strict-total-order-on-ℕ² = record
                             { _<_ = _<ₗ_
                             ; irreflexive = <ₗ-is-irreflexive
                             ; transitive = λ {p} {q} {r} → <ₗ-is-transitive {p} {q} {r}
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
 <-≤-trans {x} {y} {.y} x<y (inl (refl .y)) = inr x<y
 <-≤-trans {x} {y} {z}  x<y (inr y<z)       = inr (transitive x<y y<z)

 ≤-is-transitive : {x y z : X} → x ≤ y → y ≤ z → x ≤ z
 ≤-is-transitive {x} {.x} {z} (inl (refl .x)) y≤z = y≤z
 ≤-is-transitive {x} {y}  {z} (inr x<y)       y≤z = <-≤-trans x<y y≤z
```

### Exercise 5.3

**Prove** antisymmetry of `≤`.

```agda
 lt-lemma : (x y : X) → x < y → ¬ (y < x)
 lt-lemma x y x<y y<x = irreflexive x (transitive x<y y<x) 

 ≤-is-antisymmetric : {x y : X} → x ≤ y → y ≤ x → x ≡ y
 ≤-is-antisymmetric (inl y≡x) _ = sym y≡x
 ≤-is-antisymmetric (inr _) (inl x≡y) = x≡y
 ≤-is-antisymmetric {x} {y} (inr x<y) (inr y<x) = 𝟘-elim (irreflexive x (transitive x<y y<x))
```

### Exercise 5.4

**Show** that `≤` is strongly connected.

```agda
 ≤-is-strongly-connected : (x y : X) → (x ≤ y) ∔ (y ≤ x)
 ≤-is-strongly-connected x y = I (decidable x y)
  where
   I : is-decidable (x ≡ y) → (x ≤ y) ∔ (y ≤ x)
   I (inl x≡y)  = inr (inl x≡y)
   I (inr ¬x≡y) = II (connected ¬x≡y)
     where
       II : (x < y) ∔ (y < x) → (x ≤ y) ∔ (y ≤ x)
       II (inl x<y) = inl (inr x<y)
       II (inr y<x) = inr (inr y<x)
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

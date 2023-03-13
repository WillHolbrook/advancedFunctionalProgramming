<!--
```agda
{-# OPTIONS --without-K --safe #-}

module week7 where

open import general-notation
open import prelude
open import isomorphisms
open import Maybe
open import List
open import List-functions
open import natural-numbers-functions
```
-->
# Notes for week 7

## Question 1

**Prove** the following facts about `if_then_else_`:

```agda
ite-fact₁ : (b : Bool) → if b then true else false ≡ b
ite-fact₁ true  = refl true
ite-fact₁ false = refl false

ite-fact₂ : {X : Type} {x : X} (b : Bool) → if b then x else x ≡ x
ite-fact₂ {x = x} true  = refl x
ite-fact₂ {x = x} false = refl x

ite-fact₃ : {X : Type} {x y : X} (b : Bool)
          → if b then x else y ≡ if not b then y else x
ite-fact₃ {x = x} true  = refl x
ite-fact₃ {y = y} false = refl y

ite-fact₄ : {X : Type} {x y u v : X} (a b : Bool)
          → if a then (if b then x else y) else (if b then u else v)
          ≡ if b then (if a then x else u) else (if a then y else v)
ite-fact₄ {x = x} {y = y} true  b = refl (if b then x else y)
ite-fact₄ {u = u} {v = v} false b = refl (if b then u else v)
```

## Question 2

In this exercise, we will define an inductive type expressing what the least
upperbound of a list is.

More precisely, `xs is-bounded-by b` should satisfy:
- every element of `xs` is less than or equal to `b`;
- if `b'` is another element with the above property, then `b` is less than
or equal to `b'`.

So, for example, `[5 , 8 , 2]` is bounded by 8, but not by 9, 10, 11, ...
because these numbers are strictly bigger than necessary.

By definition, the empty list is bounded by 0.

**Complete** the definition of the inductively defined type.

```agda
data _is-bounded-by_ : List ℕ → ℕ → Type where
  zero-bounds-[] : [] is-bounded-by 0
  stays-bounded : {b : ℕ} → (n : ℕ) (ns : List ℕ)
    → ns is-bounded-by b
    → n ≤₁ b
    → (n :: ns) is-bounded-by b
  bound-increases : {b : ℕ} → (n : ℕ) (ns : List ℕ)
    → ns is-bounded-by b
    → ¬ (n ≤₁ b)
    → (n :: ns) is-bounded-by n
```

**Prove** the following examples involving `is-bounded-by`:

```agda
bounded-inductive-example₀ : [] is-bounded-by 0
bounded-inductive-example₀ = zero-bounds-[]

bounded-inductive-example₁ : (2 :: 1 :: [ 3 ]) is-bounded-by 3
bounded-inductive-example₁ = stays-bounded 2 (1 :: 3 :: [])
                               (stays-bounded 1 (3 :: [])
                                (bound-increases 3 [] zero-bounds-[] (λ z → z)) ⋆)
                               ⋆

bounded-inductive-example₂ : ¬ ((3 :: 2 :: [ 1 ]) is-bounded-by 2)
bounded-inductive-example₂ (stays-bounded .3 .(2 :: [ 1 ]) x ())
-- (stays-bounded _ _ _ ())
```

## Question 3

The cartesian product `×` satisfies the same equations as multiplication of
natural numbers:
1. `𝟘 × X ≅ X` for every type `X`;
1. `(X ∔ 𝟙) × Y ≅ (X × Y) ∔ Y` for every two types `X` and `Y`.

**Prove** the second isomorphism.

```agda
×-second-equation : (X Y : Type) → (X ∔ 𝟙) × Y ≅ (X × Y) ∔ Y
×-second-equation X Y =
 record { bijection  = f
        ; bijectivity = record { inverse = g ; η = section ; ε = retraction } }
  where
   f : (X ∔ 𝟙) × Y → (X × Y) ∔ Y
   f (inl x , y) = inl (x , y)
   f (inr ⋆ , y) = inr y

   g : (X × Y) ∔ Y → (X ∔ 𝟙) × Y
   g (inl (x , y)) = inl x , y
   g (inr y)       = inr ⋆ , y

   section : g ∘ f ∼ id
   section (inl x , y) = refl (inl x , y)
   section (inr ⋆ , y) = refl (inr ⋆ , y)

   retraction : f ∘ g ∼ id
   retraction (inl (x , y)) = refl (inl (x , y))
   retraction (inr y)       = refl (inr y)
```

## Question 4

We can define the list membership relation `∈` as follows:

```agda
data _∈_ {X : Type} : X → List X → Type where
  head-case : (x : X) (xs : List X) → x ∈ (x :: xs)
  tail-case : (x : X) (xs : List X) → x ∈ xs → (y : X) → x ∈ (y :: xs)
```

Also recall that in [List functions](../List-functions.lagda.md), we defined
`map : {X Y : Type} → (X → Y) → List X → List Y`, which applies a given function
`f : X → Y` to every element of a list `xs : List X`.  We call the resulting
list of type `List Y`, the *`f`-mapped list*.

We want you to formulate the type that describes the notion of *mapped
membership*, relative to the relation `_∈_` and operation `map`.

**Mapped membership** states that:
 > For every list `xs` and function `f`, given any member `x` of `xs`,
   we have that `f(x)` is also a member of the `f`-mapped list.

```agda
mapped-membership : Type → Type → Type
mapped-membership X Y
 = (xs : List X)(f : X → Y)(x : X) → (x ∈ xs) → f x ∈ map f xs 
```
**Translate** the statement of mapped membership to Agda code.

*Note*: We do not ask you to prove mapped membership.


## Question 5 (Hard 🌶🌶🌶)

A function `f : X → X` is *idempotent* if applying `f` twice yields the same
result as applying `f` once.

**Formalise** the above definition in Agda and **state** and **prove** that if
`f` is idempotent, then so is `map f`.

```agda
is-idempotent : {X : Type} → (f : X → X) → Type
is-idempotent {X} f = (x : X) → f (f x) ≡ f x

suc-proves-2≡1 : is-idempotent suc → 2 ≡ 1
suc-proves-2≡1 suc-idem = suc-idem 0

map-of-idempotent-function-is-idempotent : {X : Type} → (f : X → X) → is-idempotent f → is-idempotent (map f)
map-of-idempotent-function-is-idempotent f f-idem [] = refl []
map-of-idempotent-function-is-idempotent f f-idem (x :: xs) =
  map f (map f (x :: xs))     ≡⟨ refl _ ⟩
  f (f x) :: map f (map f xs) ≡⟨ ap (_::  map f (map f xs)) (f-idem x) ⟩
  f x :: map f (map f xs)     ≡⟨ ap (f x ::_) (map-of-idempotent-function-is-idempotent f f-idem xs) ⟩
  f x :: map f xs             ≡⟨ refl _ ⟩
  map f (x :: xs)             ∎

```

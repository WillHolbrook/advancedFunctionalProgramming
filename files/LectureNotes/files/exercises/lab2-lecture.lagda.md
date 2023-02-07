# Lab 2 lecture

Learning objectives:

  * Identity type
  * Proofs with the identity type
  * Emacs interactive mode

During the lab 2 lecture we will delete some of these definitions and
create them again using Agda's interactive features.

After the lab 2 lecture you will start working on the [lab2](lab2.lagda.md) problem sheet, which you should complete until the end of the week.

```agda
module exercises.lab2-lecture where

open import general-notation
open import Bool
```

The `identity-type` file, not imported here, defines the following:

```agda
data _≡_ {A : Type} : A → A → Type where
 refl : (x : A) → x ≡ x

infix 0 _≡_
```

It also defines the following functions using this.

```agda
trans : {A : Type} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans p (refl y) = p

sym : {A : Type} {x y : A} → x ≡ y → y ≡ x
sym (refl x) = refl x

ap : {A B : Type} (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
ap f (refl x) = refl (f x)
```

Here are some examples. We first define an exclusive-or function in
two ways.

```agda
_⊕_ : Bool → Bool → Bool
true  ⊕ true  = false
true  ⊕ false = true
false ⊕ true  = true
false ⊕ false = false

_⊕'_ : Bool → Bool → Bool
true  ⊕' b = not b
false ⊕' b = b

⊕-definitions-agree : (a b : Bool) → a ⊕ b ≡ a ⊕' b
⊕-definitions-agree true true   = refl false
⊕-definitions-agree true false  = refl true
⊕-definitions-agree false true  = refl true
⊕-definitions-agree false false = refl false
```

Here are some laws.

```
⊕-commutative : (a b : Bool) → a ⊕ b ≡ b ⊕ a
⊕-commutative true true   = refl false
⊕-commutative true false  = refl true
⊕-commutative false true  = refl true
⊕-commutative false false = refl false

⊕'-law₀ : (b : Bool) → not b ≡ b ⊕' true
⊕'-law₀ true  = refl false
⊕'-law₀ false = refl true

⊕'-law₁ : (b : Bool) → b ≡ b ⊕' false
⊕'-law₁ true  = refl true
⊕'-law₁ false = refl false

⊕'-commutative : (a b : Bool) → a ⊕' b ≡ b ⊕' a
⊕'-commutative true  b = ⊕'-law₀ b
⊕'-commutative false b = ⊕'-law₁ b

⊕-self-inverse : (b : Bool) → b ⊕ b ≡ false
⊕-self-inverse true  = refl false
⊕-self-inverse false = refl false


⊕-associative : (a b c : Bool) → a ⊕ (b ⊕ c) ≡ (a ⊕ b) ⊕ c
⊕-associative true  true  true  = refl true
⊕-associative true  true  false = refl false
⊕-associative true  false true  = refl false
⊕-associative true  false false = refl true
⊕-associative false true  true  = refl false
⊕-associative false true  false = refl true
⊕-associative false false true  = refl true
⊕-associative false false false = refl false
```

We can get a shorter proof with our cleverer definition of
exclusive-or, using two laws for negation:

```
not-involutive : (b : Bool) → not (not b) ≡ b
not-involutive true  = refl true
not-involutive false = refl false

⊕'-law₂ : (a b : Bool) → not (a ⊕' b) ≡ (not a) ⊕' b
⊕'-law₂ true  b = not-involutive b
⊕'-law₂ false b = refl (not b)

⊕'-associative : (a b c : Bool) → a ⊕' (b ⊕' c) ≡ (a ⊕' b) ⊕' c
⊕'-associative true  b c = ⊕'-law₂ b c
⊕'-associative false b c = refl (b ⊕' c)
```

Natural numbers:

```agda
open import natural-numbers-type

max : ℕ → ℕ → ℕ
max 0       n       = n
max (suc m) 0       = suc m
max (suc m) (suc n) = suc (max m n)

max-with-0 : (y : ℕ) → y ≡ max y 0
max-with-0 0       = refl 0
max-with-0 (suc y) = refl (suc y)

max-commutative : (x y : ℕ) → max x y ≡ max y x
max-commutative 0       y       = max-with-0 y
max-commutative (suc x) 0       = refl (suc x)
max-commutative (suc x) (suc y) = goal
 where
  IH : max x y ≡ max y x
  IH = max-commutative x y

  goal : suc (max x y) ≡ suc (max y x)
  goal = ap suc IH
```

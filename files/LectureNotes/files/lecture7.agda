--
--  lecture7.agda
--

--
--  Attendance: 55914404
--

module lecture7 where

open import prelude
open import isomorphisms
open import natural-numbers-functions
open import function-extensionality
open import List-functions 
open import Fin
open import Vector

ite-fact₁ : (b : Bool) → if b then true else false ≡ b
ite-fact₁ true = refl true
ite-fact₁ false = refl _

ite-fact₂ : {X : Type} {x : X} (b : Bool) → if b then x else x ≡ x
ite-fact₂ true = refl _
ite-fact₂ false = refl _

ite-fact₃ : {X : Type} {x y : X} (b : Bool)
          → if b then x else y ≡ if not b then y else x
ite-fact₃ true = refl _
ite-fact₃ false = refl _

ite-fact₄ : {X : Type} {x y u v : X} (a b : Bool)
          → if a then (if b then x else y) else (if b then u else v)
          ≡ if b then (if a then x else u) else (if a then y else v)
ite-fact₄ true b = refl _
ite-fact₄ false b = refl _

--
--  Question 2 
--

data _is-bounded-by_ : List ℕ → ℕ → Type where
  zero-bounds-[] : [] is-bounded-by zero
  stays-bounded : {b : ℕ} → (n : ℕ) (ns : List ℕ)
    → ns is-bounded-by b
    → n ≤₁ b
    → (n :: ns) is-bounded-by b
  bound-increases : {b : ℕ} → (n : ℕ) (ns : List ℕ)
    → ns is-bounded-by b
    → ¬ (n ≤₁ b)
    → (n :: ns) is-bounded-by n

-- _is-bounded-by'_ : List ℕ → ℕ → Type
-- [] is-bounded-by' zero = 𝟙
-- [] is-bounded-by' suc n = 𝟘
-- (n :: ns) is-bounded-by' b = {!!}

bounded-inductive-example₀ : [] is-bounded-by 0
bounded-inductive-example₀ = zero-bounds-[]

bounded-inductive-example₁ : (2 :: 1 :: [ 3 ]) is-bounded-by 3
bounded-inductive-example₁ = stays-bounded 2 (1 :: 3 :: [])
                               (stays-bounded 1 (3 :: [])
                                (bound-increases 3 [] zero-bounds-[] (λ z → z)) ⋆)
                               ⋆

bounded-inductive-example₂ : ¬ ((3 :: 2 :: [ 1 ]) is-bounded-by 2)
bounded-inductive-example₂ (stays-bounded .3 .(2 :: [ 1 ]) _ 3≤2) = 3≤2

--
--  Question 3
--

×-second-equation : (X Y : Type) → (X ∔ 𝟙) × Y ≅ (X × Y) ∔ Y
×-second-equation X Y =
 record { bijection  = f
        ; bijectivity = record { inverse = g ; η = section ; ε = retraction } }
  where
   f : (X ∔ 𝟙) × Y → (X × Y) ∔ Y
   f (inl x , y) = inl (x , y)
   f (inr ∙ , y) = inr y

   g : (X × Y) ∔ Y → (X ∔ 𝟙) × Y
   g (inl (x , y)) = inl x , y
   g (inr y) = inr ⋆ , y

   section : g ∘ f ∼ id
   section (inl x , y) = refl _
   section (inr ∙ , y) = refl _

   retraction : f ∘ g ∼ id
   retraction (inl (x , y)) = refl _
   retraction (inr y) = refl _

--
--  Question 4
--

data _∈_ {X : Type} : X → List X → Type where
  head-case : (x : X) (xs : List X) → x ∈ (x :: xs)
  tail-case : (x : X) (xs : List X) → x ∈ xs → (y : X) → x ∈ (y :: xs)

-- **Mapped membership** states that:
--  > For every list `xs` and function `f`, given any member `x` of `xs`,
--    we have that `f(x)` is also a member of the `f`-mapped list.

mapped-membership : Type → Type → Type
mapped-membership X Y = (xs : List X) (f : X → Y) (x : X) → x ∈ xs → f x ∈ map f xs

--
--  Question 5
--

-- A function `f : X → X` is *idempotent* if applying `f` twice yields the same
-- result as applying `f` once.

-- **Formalise** the above definition in Agda and **state** and **prove** that if
-- `f` is idempotent, then so is `map f`.

is-idempotent : (X : Type) (f : X → X) → Type 
is-idempotent X f = (x : X) → f (f x) ≡ f x

-- Too strong!  This is the claim that *every* function is idempotent..
everyone-is-idempotent : (X : Type) (f : X → X) (x : X) → f (f x) ≡ f x
everyone-is-idempotent = {!!}

-- This function is *not* idempotent
suc-is-idempotent : is-idempotent ℕ suc
suc-is-idempotent = {!!}

id-is-idempotent : (X : Type) → is-idempotent X (λ x → x)
id-is-idempotent X x = refl x 

map-of-idempotent-function-is-idempotent : (X : Type) (f : X → X) → is-idempotent X f → is-idempotent (List X) (map f) 
map-of-idempotent-function-is-idempotent X f is-idem-f = {!!}



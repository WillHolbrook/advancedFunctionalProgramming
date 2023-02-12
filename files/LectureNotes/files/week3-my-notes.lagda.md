

```agda
module week3-my-notes where

open import prelude

my-forall : {A : Type} (f : A → Bool) → List A → Bool
my-forall f [] = true
my-forall f (x :: xs) = f x && (my-forall f xs)

EQᴮᴼᴼᴸ : (ℕ → ℕ) → (ℕ → ℕ) → Bool
EQᴮᴼᴼᴸ f g = {!!}

EQᵀ : (ℕ → ℕ) → (ℕ → ℕ) → Type
EQᵀ f g = (n : ℕ) -> f n ≡ g n

is-decidable : Type → Type
is-decidable A = A ∔ ¬ A

is-decidable-𝟘 : is-decidable 𝟘
is-decidable-𝟘 = inr id
-- where id : 𝟘 → 𝟘

is-decidable-predicate : {A : Type} (P : A → Type) → (a : A) → is-decidable (P a)
is-decidable-predicate P a = {!!}

is-decidable-relation : {A : Type} (R : A → A → Type) → (a b : A) → is-decidable (R a b)
is-decidable-relation R a b = {!!}
```

Decidable types:

ℕ, Bool, 𝟙, 𝟘

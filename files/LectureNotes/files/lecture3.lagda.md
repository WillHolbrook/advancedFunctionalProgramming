<!--
```agda
{-# OPTIONS --without-K --safe #-}

module lecture3 where

open import general-notation
open import prelude
```
-->
typical maths symbols:

and - ∧
or - ∨
implies - →
forall - ∀
exists - ∃

  

```agda
andT : Type → Type → Type
andT A B = A × B

orT : Type → Type → Type
orT A B = A ∔ B

implies : Type → Type → Type
implies A B = A → B

forallT : (A : Type) (P : A → Type) → Type
forallT A P = (a : A) → P a

existsT : (A : Type) (P : A → Type) → Type
existsT A P = Σ a ꞉ A , P a

is-decidable : Type → Type
is-decidable A = A ∔ ¬ A
```

### "Classification" of decidable types
```agda
classify-decidable : (A : Type) → is-decidable A → Σ b ꞉ Bool , (A ⇔ b ≡ true)
classify-decidable A (inl a) = true , ((λ _ → refl true) , (λ _ → a))
classify-decidable A (inr p) = false , ((λ a → 𝟘-elim (p a)) , λ {()})


is-decidable-predicate : {A : Type} (P : A → Type) → Type
is-decidable-predicate {A} P = (a : A) → is-decidable (P a)

is-decidable-relation : {A : Type} (R : A → A → Type) → Type
is-decidable-relation {A} R = (a b : A) → is-decidable (R a b)


data _≤_ : ℕ → ℕ → Type where
  0≤ : {n : ℕ} → 0 ≤ n
  S≤ : {m n : ℕ} → m ≤ n → suc m ≤ suc n

_ : 2 ≤ 4
_ = S≤ (S≤ 0≤)

example : ¬ (4 ≤ 2)
example (S≤ (S≤ ()))

≤-is-decidable : is-decidable-relation _≤_
≤-is-decidable zero m = inl 0≤
≤-is-decidable (suc n) zero = inr λ {()}
≤-is-decidable (suc n) (suc m) = {!!}
  where
    lem : is-decidable (m ≤ n) → is-decidable (suc m ≤ suc n)
    lem (inl m≤n) = inl (S≤ m≤n)
    lem (inr m≰n) = inr {!λ x → ?!}
```

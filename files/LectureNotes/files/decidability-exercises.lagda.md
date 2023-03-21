```agda
{-# OPTIONS --without-K --safe #-}

module decidability-exercises where

open import prelude
open import decidability
```

**Exercises.** If two types `A` and `B` are exhaustively searchable types, then so are the types `A × B` and `A + B`. Moreover, if `X` is an exhaustively searchable type and `A : X → Type` is a family of types, and the type `A x` is exhaustively searchable for each `x : X`, then the type `Σ x ꞉ X , A x` is exhaustively searchable.

```agda
and-exhaustively-searchable : {A B : Type}
                            → is-exhaustively-searchable A
                            → is-exhaustively-searchable B
                            → is-exhaustively-searchable (A × B)
and-exhaustively-searchable {A} {B} a-exhas-search b-exhaus-search P P-is-decidable = {!!}

or-exhaustively-searchable : {A B : Type}
                           → is-exhaustively-searchable A
                           → is-exhaustively-searchable B
                           → is-exhaustively-searchable (A ∔ B)
or-exhaustively-searchable {A} {B} a-exhas-search b-exhaus-search P P-is-decidable = {!!}

exists-exhaustively-searchable : {X : Type}
                               → is-exhaustively-searchable X
                               → (A : X → Type)
                               → (x : X) → is-exhaustively-searchable (A x)
                               → is-exhaustively-searchable (Σ x ꞉ X , A x)
exists-exhaustively-searchable {X} x-exhas-serarch A x ax-exhas-serarch P P-is-decidable = {!!}
```

**Exercise Done**. Show, in Agda, that a type `X` has decidable equality if and only if there is a function `X → X → Bool` that checks whether two elements of `X` are equal or not.

```agda
false-is-not-true : ¬ (false ≡ true)
false-is-not-true ()

lemma₁ : {X : Type}
       → ((x y : X) → Σ f ꞉ (X → X → Bool) , (f x y ≡ true ⇔ x ≡ y))
       → (has-decidable-equality X)
lemma₁ {X} func x y = I (func x y)
  where
    I : Σ f ꞉ (X → X → Bool) , (f x y ≡ true ⇔ x ≡ y) → (x ≡ y) ∔ (x ≡ y → 𝟘)
    I (f , feq₁ , feq₂) with f x y
    I (f , feq₁ , feq₂) | true = inl (feq₁ (refl true))
    I (f , feq₁ , feq₂) | false = inr (false-is-not-true ∘ feq₂)

lemma₂ : {X : Type}
       → (has-decidable-equality X)
       → ((x y : X) → Σ f ꞉ (X → X → Bool) , (f x y ≡ true ⇔ x ≡ y))
lemma₂ dec x y with dec x y
lemma₂ dec x .x | inl (refl .x) =
  (λ a b → true) ,
  (λ _ → refl x) , (λ _ → refl true)
lemma₂ dec x y | inr ¬x≡y =
  (λ a b → false) ,
  (λ f≡t → 𝟘-elim (false-is-not-true f≡t)) , λ x≡y → 𝟘-elim (¬x≡y x≡y)

decidable-equality-func : {X : Type}                        
                        → (has-decidable-equality X)
                        ⇔ ((x y : X) → Σ f ꞉ (X → X → Bool) , (f x y ≡ true ⇔ x ≡ y))
decidable-equality-func = lemma₂ , lemma₁

```

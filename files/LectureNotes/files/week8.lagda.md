<!--
```agda
{-# OPTIONS --without-K --safe #-}

module week8 where

open import prelude
open import Maybe
open import List
open import List-functions
open import decidability
```
-->
# Notes for week 8

```agda
module Regex (A : Type) (compare : has-decidable-equality A) where
  data RegExp : Type where
    ∅ : RegExp --Empty
    `_ : A → RegExp --Single
    _‵_ : (ρ : RegExp)(σ : RegExp) → RegExp -- Sequential Composition
    _∪_ : (ρ : RegExp)(σ : RegExp) → RegExp -- Or
    _+ : (ρ : RegExp) → RegExp --One or more

  data _accepts_ : RegExp → List A → Type where
    acc-` : (a : A) → (` a) accepts (a :: [])
    acc-‵ : {ρ σ : RegExp} {as bs : List A}
      → ρ accepts as
      → σ accepts bs
      → (ρ ‵ σ) accepts (as ++ bs)
    acc-∪ : {ρ σ : RegExp} {as : List A}
      → (ρ accepts as) ∔ (σ accepts as)
      → (ρ ∪ σ) accepts as
    acc-+-one : {ρ : RegExp}{as : List A}
      → ρ accepts as
      → (ρ +) accepts as
    acc-+-many : {ρ : RegExp}{as ts : List A}
      → ρ accepts as
      → (ρ +) accepts ts
      → (ρ +) accepts (as ++ ts)

  Stack : Type
  Stack = List RegExp

  _stack-accepts_ : Stack → List A → Type

  record MatchResult (ρ : RegExp)(ρs : Stack)(as : List A) : Type where
    constructor ⟨⟨_,_,_,_,_⟩⟩
    inductive
    field
      hd : List A
      tl : List A
      ρ-acc-suf : ρ accepts hd
      ρs-acc-tl : ρs stack-accepts tl
      recons : as ≡ hd ++ tl

  
  [] stack-accepts [] = 𝟙
  [] stack-accepts (_ :: _) = 𝟘
  (ρ :: ρs) stack-accepts as = MatchResult ρ ρs as

  match-stack : (ρs : Stack)(as : List A)
    → Maybe (ρs stack-accepts as)

  match : (ρ : RegExp)(ρs : Stack)(as : List A)
    → Maybe (MatchResult ρ ρs as)
  match ∅ ρs as = nothing
  match (` x) ρs [] = nothing
  match (` x) ρs (y :: as) =
    ∔-nondep-elim
      (λ { (refl .x) → {!match-stack ρs as >>= !}})
      (λ _ → nothing)
      (compare x y)
  match (ρ ‵ ρ₁) ρs as = {!!}
  match (ρ ∪ ρ₁) ρs as = {!!}
  match (ρ +) ρs as = {!!}

  match-stack [] [] = just ⋆
  match-stack [] (_ :: _) = nothing
  match-stack (ρ :: ρs) as = match ρ ρs as

  matches : (ρ : RegExp)(as : List A) → Maybe (ρ accepts as)
  matches ∅ as = nothing
  matches (` x) [] = nothing
  matches (` x) (y :: []) with compare x y
  matches (` x) (.x :: []) | inl (refl .x) = just (acc-` x)
  matches (` x) (y :: [])  | inr ¬eq = nothing
  matches (` x) (_ :: _ :: _) = nothing
  matches (ρ ‵ σ) as = {!!}
    where
      I : (xs : List A)(ys : List A) → Maybe ((ρ ‵ σ) accepts (xs ++ ys))
      I xs [] with matches ρ xs | matches σ []
      I xs [] | nothing | b = nothing
      I xs [] | just prf | nothing = nothing
      I xs [] | just prf | just prf2 = just (acc-‵ prf prf2)
      I xs (y :: ys) = {!!}
  matches (ρ ∪ σ) as = {!!}
  matches (ρ +) as = {!!}

module Example where
  data Alph : Type where
    A : Alph
    B : Alph

  Alph-has-decidable-equality : has-decidable-equality Alph
  Alph-has-decidable-equality A A = inl (refl A)
  Alph-has-decidable-equality A B = inr (λ ())
  Alph-has-decidable-equality B A = inr (λ ())
  Alph-has-decidable-equality B B = inl (refl B)

  open Regex Alph Alph-has-decidable-equality

  ρ : RegExp
  ρ = ((` A) ∪ (` B)) +

  as : List Alph
  as = A :: A :: B :: []

  ρ-acc-s : ρ accepts as
  ρ-acc-s = acc-+-many (acc-∪ (inl (acc-` A)))
              (acc-+-many (acc-∪ (inl (acc-` A)))
               (acc-+-one (acc-∪ (inr (acc-` B)))))
```

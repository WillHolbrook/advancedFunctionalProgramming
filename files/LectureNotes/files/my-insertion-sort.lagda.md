```agda
{-# OPTIONS --without-K --safe #-}

module my-insertion-sort where

open import prelude
open import isomorphisms
open import List-functions
open import iso-utils
open import strict-total-order
open import sorting

module InsertionSort (X : Type) (τ : StrictTotalOrder X) where
  open _IsPermutationOf_
  open StrictTotalOrder τ
  open _≅_

  insert : X → List X → List X
  insert y [] = y :: []
  insert y (x :: xs) with trichotomy x y
  insert y (x :: xs) | inl x<y = x :: insert y xs
  insert y (x :: xs) | inr x≥y = y :: x :: xs

  insert-all : List X → List X → List X
  insert-all [] xs = xs
  insert-all (y :: ys) xs = insert y (insert-all ys xs)

  insertion-sort : List X → List X
  insertion-sort xs = insert-all xs []

  -- Proving that insertion-sort gives a sorted list

  insert-is-sorted : (y : X) (xs : List X) → Sorted τ xs → Sorted τ (insert y xs)
  insert-is-sorted y [] nil-sorted = sing-sorted
  insert-is-sorted y (x :: []) sing-sorted with trichotomy x y
  insert-is-sorted y (x :: []) sing-sorted | inl x<y = adj-sorted sing-sorted (inr x<y)
  insert-is-sorted y (x :: []) sing-sorted | inr x≥y = adj-sorted sing-sorted x≥y
  insert-is-sorted y (z :: x :: xs) (adj-sorted s z≤x) with trichotomy z y
  insert-is-sorted y (z :: x :: xs) (adj-sorted s z≤x) | inl z<y with trichotomy x y | insert-is-sorted y (x :: xs) s
  insert-is-sorted y (z :: x :: xs) (adj-sorted s z≤x) | inl z<y | inl x<y | s' = adj-sorted s' z≤x
  insert-is-sorted y (z :: x :: xs) (adj-sorted s z≤x) | inl z<y | inr x≥y | s' = adj-sorted s' (inr z<y)
  insert-is-sorted y (z :: x :: xs) (adj-sorted s z≤x) | inr z≥y = adj-sorted (adj-sorted s z≤x) z≥y

  insert-all-is-sorted : (ys xs : List X) → Sorted τ xs → Sorted τ (insert-all ys xs)
  insert-all-is-sorted [] xs s = s
  insert-all-is-sorted (y :: ys) xs s = insert-is-sorted y (insert-all ys xs) (insert-all-is-sorted ys xs s)

  insertion-sort-is-sorted : (ys : List X) → Sorted τ (insertion-sort ys)
  insertion-sort-is-sorted ys = insert-all-is-sorted ys [] nil-sorted

  -- Isomorphism on postions

  insert-pos-iso : (y : X) (xs : List X) → Pos (insert y xs) ≅ 𝟙 ∔ Pos xs
  insert-pos-iso y [] = id-iso (𝟙 ∔ 𝟘)
  insert-pos-iso y (x :: xs) with trichotomy x y
  insert-pos-iso y (x :: xs) | inl x<y = 
    𝟙 ∔ Pos (insert y xs) ≅⟨ ∔-pair-iso (id-iso 𝟙) (insert-pos-iso y xs) ⟩
    𝟙 ∔ 𝟙 ∔ Pos xs ≅⟨ ∔-left-swap-iso 𝟙 𝟙 (Pos xs) ⟩
    -- x y xs
    𝟙 ∔ 𝟙 ∔ Pos xs ∎ᵢ
    -- y x xs
  insert-pos-iso y (x :: xs) | inr x≥y = id-iso (𝟙 ∔ 𝟙 ∔ Pos xs)
```

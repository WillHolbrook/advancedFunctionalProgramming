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

  insert-all-pos-iso : (xs ys : List X) → Pos (insert-all xs ys) ≅ Pos (xs ++ ys)
  insert-all-pos-iso [] ys = id-iso (Pos ys)
  insert-all-pos-iso (x :: xs) ys =
   Pos (insert-all (x :: xs) ys) ≅⟨ insert-pos-iso x (insert-all xs ys) ⟩
   𝟙 ∔ Pos (insert-all xs ys)    ≅⟨ ∔-pair-iso (id-iso 𝟙) (insert-all-pos-iso xs ys) ⟩
   𝟙 ∔ Pos (xs ++ ys)            ≅⟨ id-iso _ ⟩
   Pos ((x :: xs) ++ ys) ∎ᵢ    

  -- Inhabitant Equality

  pos-swap-lemma : (y x : X) (xs : List X) (p : Pos (x :: y :: xs))
    → Inhab (x :: y :: xs) p ≡ Inhab (y :: x :: xs) (bijection (∔-left-swap-iso 𝟙 𝟙 (Pos xs)) p)
  pos-swap-lemma y x xs (inl ⋆) = refl x
  pos-swap-lemma y x xs (inr (inl ⋆)) = refl y
  pos-swap-lemma y x xs (inr (inr p)) = refl (Inhab xs p)

  insert-inhab-eq : (y : X) (xs : List X) (p : Pos (insert y xs))
    → Inhab (insert y xs) p ≡ Inhab (y :: xs) (bijection (insert-pos-iso y xs) p)
  insert-inhab-eq y [] (inl ⋆) = refl y
  insert-inhab-eq y (x :: xs) p with trichotomy x y
  insert-inhab-eq y (x :: xs) (inl ⋆) | inl x<y = refl x
  insert-inhab-eq y (x :: xs) (inr p) | inl x<y =    
   Inhab (x :: insert y xs) (inr p)                    ≡⟨ refl _ ⟩
   Inhab (insert y xs) p                               ≡⟨ insert-inhab-eq y xs p ⟩
   Inhab (y :: xs) (bijection (insert-pos-iso y xs) p) ≡⟨ refl _ ⟩
   Inhab (x :: y :: xs) (inr (bijection (insert-pos-iso y xs) p))
     ≡⟨ pos-swap-lemma y x xs ((inr (bijection (insert-pos-iso y xs) p))) ⟩
   Inhab (y :: x :: xs)
   (bijection (∔-left-swap-iso 𝟙 𝟙 (Pos xs))
     (inr (bijection (insert-pos-iso y xs) p))) ∎
  insert-inhab-eq y (x :: xs) p | inr x≥y = refl (Inhab (y :: x :: xs) p)

  inhab-ext-lemma : (x : X) (xs ys : List X) 
    → (α : Pos xs ≅ Pos ys)
    → (e : (p : Pos xs) → Inhab xs p ≡ Inhab ys (bijection α p))
    → (p : Pos (x :: xs))
    → Inhab (x :: xs) p ≡ Inhab (x :: ys) (bijection (∔-pair-iso (id-iso 𝟙) α) p)
  inhab-ext-lemma x xs ys α e (inl ⋆) = refl x
  inhab-ext-lemma x xs ys α e (inr p) = e p

  insert-all-inhab-eq : (xs ys : List X) (p : Pos (insert-all xs ys))
    → Inhab (insert-all xs ys) p ≡
      Inhab (xs ++ ys) (bijection (insert-all-pos-iso xs ys) p)
  insert-all-inhab-eq [] ys p = refl (Inhab ys p)
  insert-all-inhab-eq (x :: xs) ys p = 
    Inhab (insert x (insert-all xs ys)) p
      ≡⟨ insert-inhab-eq x (insert-all xs ys) p ⟩
    Inhab (x :: insert-all xs ys) (bijection (insert-pos-iso x (insert-all xs ys)) p)
      ≡⟨ inhab-ext-lemma x (insert-all xs ys) (xs ++ ys)
           (insert-all-pos-iso xs ys)
           (λ p → insert-all-inhab-eq xs ys p)
          (bijection (insert-pos-iso x (insert-all xs ys)) p) ⟩ 
    Inhab (x :: xs ++ ys) (bijection (∔-pair-iso (id-iso 𝟙) (insert-all-pos-iso xs ys))
                          (bijection (insert-pos-iso x (insert-all xs ys)) p)) ∎


  -- Insertion gives permutations

  insert-perm : (y : X) (xs : List X ) →
    (insert y xs) IsPermutationOf (y :: xs)
  insert-perm y xs = record { pos-iso = insert-pos-iso y xs ; inhab-eq = insert-inhab-eq y xs }

  insert-all-perm : (ys xs : List X) →
    (insert-all ys xs) IsPermutationOf (ys ++ xs)
  insert-all-perm ys xs = record { pos-iso = insert-all-pos-iso ys xs ; inhab-eq = insert-all-inhab-eq ys xs }

  insertion-sort-perm : (xs : List X) →
    (insertion-sort xs) IsPermutationOf xs
  insertion-sort-perm xs =
    transport (λ l → insertion-sort xs IsPermutationOf l)
      ([]-right-neutral xs) (insert-all-perm xs [])

  -- Insertion Sort is a sorting algorithm

  InsertionSortingAlgo : SortingAlgorithm τ
  InsertionSortingAlgo = record {
    sort = insertion-sort ;
    sort-is-sorted = insertion-sort-is-sorted ;
    sort-is-permutation = insertion-sort-perm
    }
```
9:43 7.



```agda
{-# OPTIONS --without-K --safe --auto-inline #-}

module list-filter-functions where

open import prelude
open import natural-numbers-functions
open import List-functions

filter : {X : Type} (P : X → Bool) → List X → List X
filter P [] = []
filter P (x :: xs) = if (P x) then (x :: filter P xs) else (filter P xs)

pop-list : {X : Type} → List X → List X
pop-list [] = []
pop-list (x :: xs) = xs

length-of-filter : {A : Type} (P : A → Bool) (xs : List A)
                 → length (filter P xs) ≤ length xs
length-of-filter P []        = 0-smallest
length-of-filter P (x :: xs) = Bool-elim goal-statement true-case false-case (P x)
 where
  ys = filter P xs
  
  goal-statement : Bool → Type
  goal-statement b = length (if b then (x :: ys) else ys) ≤ length (x :: xs)

  IH : length ys ≤ length xs
  IH = length-of-filter P xs

  false-case : length ys ≤ length (x :: xs)
  false-case = ≤-trans (length ys) (length xs) (length (x :: xs))
                 IH (≤-suc-lemma (length xs))

  true-case : length (x :: ys) ≤ length (x :: xs)
  true-case = suc-preserves-≤ IH
 

pop-list-under-filter : {X : Type}(x : X)(xs : List X)(P : X → Bool) → filter P (x :: xs) ≡ x :: xs → filter P xs ≡ xs
pop-list-under-filter x [] P eq = refl []
pop-list-under-filter x (y :: xs) P eq with P x
pop-list-under-filter x (y :: xs) P eq | true = ap pop-list eq
pop-list-under-filter x (y :: xs) P eq | false with P y
pop-list-under-filter x (y :: xs) P eq | false | true
  = 𝟘-elim (<-imp-¬eq (suc-≤-imp-< (length-of-filter P xs)) (ap (pred ∘ length) eq))
pop-list-under-filter x (y :: xs) P eq | false | false = 𝟘-elim (<-imp-¬eq (suc-≤-imp-< (suc-on-right-≤ (length-of-filter P xs))) (ap length eq))
```

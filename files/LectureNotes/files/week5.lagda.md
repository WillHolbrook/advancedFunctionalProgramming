<!--
```agda
{-# OPTIONS --without-K --safe #-}

module week5 where

open import general-notation
open import prelude
open import isomorphisms
open import Maybe
open import List
open import List-functions
```
-->
```agda
is-even : ℕ → Type
is-even zero = 𝟙
is-even (suc zero) = 𝟘
is-even (suc (suc n)) = is-even n

even-or-odd : (n : ℕ) → is-even n ∔ ¬(is-even n)
even-or-odd zero = inl ⋆
even-or-odd (suc zero) = inr (λ x → x)
even-or-odd (suc (suc n)) = even-or-odd n

right-unit : (n : ℕ) → n + 0 ≡ n
right-unit zero = refl zero
right-unit (suc n) = ap suc (right-unit n)

Bool-isomorphism : Bool ≅ 𝟙 ∔ 𝟙
Bool-isomorphism = record { bijection = f ; bijectivity = f-is-bijection }
 where
  f : Bool → 𝟙 ∔ 𝟙
  f true = inl ⋆
  f false = inr ⋆

  g : 𝟙 ∔ 𝟙 → Bool
  g (inl ⋆) = true
  g (inr ⋆) = false

  gf : g ∘ f ∼ id
  gf true = refl true
  gf false = refl false

  fg : f ∘ g ∼ id
  fg (inl ⋆) = refl (inl ⋆)
  fg (inr ⋆) = refl (inr ⋆)

  f-is-bijection : is-bijection f
  f-is-bijection = record { inverse = g ; η = gf ; ε = fg }


Maybe-isomorphism' : (X : Type) → Maybe X ≅ 𝟙 ∔ X
Maybe-isomorphism' X = record { bijection = f ; bijectivity = f-is-bijection }
 where
  f : Maybe X → 𝟙 ∔ X
  f nothing = inl ⋆
  f (just x) = inr x

  g : 𝟙 ∔ X → Maybe X
  g (inl ⋆) = nothing
  g (inr x) = just x

  gf : g ∘ f ∼ id
  gf nothing = refl nothing
  gf (just x) = refl (just x)

  fg : f ∘ g ∼ id
  fg (inl ⋆) = refl (inl ⋆)
  fg (inr x) = refl (inr x)

  f-is-bijection : is-bijection f
  f-is-bijection = record { inverse = g ; η = gf ; ε = fg }

Σ-combine : {A B : Type} {a c : A} {b d : B} → a ≡ c → b ≡ d → (a , b) ≡ (c , d)
Σ-combine {A} {B} {a} {.a} {b} {.b} (refl .a) (refl .b) = refl (a , b)

Σ-ap : {A B C D : Type} {x y : A} {w z : C} (f : A → B) (g : C → D) → (x , w) ≡ (y , z) → (f x , g w) ≡ (f y , g z)
Σ-ap f g eq = Σ-combine (ap (f ∘ fst) eq) (ap (g ∘ snd) eq)

Σ-ap-rhs : {A B C D : Type} {x y : A} {w z : C} (g : C → D) → (x , w) ≡ (y , z) → (x , g w) ≡ (y , g z)
Σ-ap-rhs g = Σ-ap id g

Σ-ap-lhs : {A B C D : Type} {x y : A} {w z : C} (f : A → B) → (x , w) ≡ (y , z) → (f x , w) ≡ (f y , z)
Σ-ap-lhs f = Σ-ap f id

lists-from-vectors : {A : Type} → List A  ≅ (Σ n ꞉ ℕ , Vector A n)
lists-from-vectors {A} = record { bijection = f ; bijectivity = f-is-bijection }
 where
  f : List A → Σ n ꞉ ℕ , Vector A n
  f [] = zero , []
  f (x :: xs) with f xs
  ... | n , vec-xs = (suc n) , (x :: vec-xs)

  g : Σ n ꞉ ℕ , Vector A n → List A
  g (zero , []) = []
  g (suc n , x :: vec-xs) = x :: (g (n , vec-xs))

  gf : g ∘ f ∼ id
  gf [] = refl []
  gf (x :: xs) = ap (_::_ x) (gf xs)

  fg : f ∘ g ∼ id
  fg (zero , []) = refl (zero , [])
  fg (suc n , x :: vec-xs) with (f ∘ g) (n , vec-xs) | fg (n , vec-xs)
  ... | .(n , vec-xs) | refl .(n , vec-xs) = refl (suc n , x :: vec-xs)
  -- = {!!}
  --   where
  --     IH : f (g (n , vec-xs)) ≡ (n , vec-xs)
  --     IH = fg (n , vec-xs)
  

--ap (suc ∘ fst) z : suc (fst (f (g (n , vec-xs)))) ≡ suc n
  f-is-bijection : is-bijection f
  f-is-bijection = record { inverse = g ; η = gf ; ε = fg }

pred : ℕ → ℕ
pred zero = zero
pred (suc n) = n

ap-pred-ap-suc-cancel : {a b : ℕ} {eq : a ≡ b} → ap pred (ap suc eq) ≡ eq
ap-pred-ap-suc-cancel {a} {.a} {refl .a} = refl (refl a)

pair-eq : {A : Type} {B : A → Type} (z : Σ {A} B) → ((fst z) , (snd z)) ≡ z
pair-eq z = refl z

vectors-from-lists : {A : Type} {n : ℕ} → Vector A n ≅ (Σ xs ꞉ List A , length xs ≡ n)
vectors-from-lists {A} {n} = record { bijection = f n ; bijectivity = f-is-bijection n }
 where
  f : (n : ℕ) → Vector A n → (Σ xs ꞉ List A , (length xs ≡ n))
  f zero [] = [] , refl zero
  f (suc n) (x :: vec-xs) with f n vec-xs
  ... | xs , refl .(length xs) = (x :: xs) , (refl (length (x :: xs)))

-- = (x :: fst IH) , ap suc (snd IH)
--     where
--       IH : Σ xs ꞉ List A , (length xs ≡ n)
--       IH = f n vec-xs


  g : (n : ℕ) → (Σ xs ꞉ List A , (length xs ≡ n)) → Vector A n
  g 0 ([] , refl 0) = []
  g .(length (x :: xs)) (x :: xs , refl .(length (x :: xs)))
    = x :: (g (length xs) (xs , refl (length xs)))
  -- g zero ([] , refl zero) = []
  -- g (suc .(length xs)) (x :: xs , refl .(suc (length xs))) = x :: (g (length xs) (xs , refl (length xs)))
  --= x :: g n (xs , ap pred suc-eq) 

  gf : (n : ℕ) →  ((g n) ∘ (f n)) ∼ id
  gf zero [] = refl []
  gf (suc n) (x :: vec-xs) with ((g n) ∘ (f n)) vec-xs | gf n vec-xs
  gf (suc n) (x :: vec-xs) | .vec-xs | refl .vec-xs = {!!}


-- with f n vec-xs
--   gf (suc .(length xs)) (x :: vec-xs)
--     | xs , refl .(length xs)
--     with
--       g (length xs) (f (length xs) vec-xs)
--       | gf (length xs) vec-xs
--   -- gf (suc .(length xs)) (x :: vec-xs)
--   --   | xs , refl .(length xs)
--   --   | a
--   --   | b
--   gf (suc .(length xs)) (x :: vec-xs) | xs , refl .(length xs) | a | prf = ap (x ::_) {!!}
--       -- where
      --   IH : g (length xs) (f (length xs) vec-xs) ≡ vec-xs
      --   IH = gf (length xs) vec-xs

      --   I : g (length xs) (f (length xs) vec-xs) ≡ g (length xs) (xs , refl (length xs))
      --   I = ap (g (length xs)) {!!}
  -- gf (suc .(length xs)) (x :: .(g (length xs) (xs , refl (length xs)))) |
  --   xs , refl .(length xs) |
  --   .xs , eq |
  --   refl .(g (length xs) (.xs , refl .(length xs)))
  --   = ap (x ::_) (ap (g (length xs)) {!!})
    -- where
    --  I : a ≡ g (length xs) (f (length xs) vec-xs)
    --  I = {!!}


  

-- with (g (length xs) ∘ f (length xs)) vec-xs | gf (length xs) vec-xs
--   gf (suc .(length xs)) (x :: vec-xs) | xs , refl .(length xs) | .vec-xs | refl .vec-xs = {!!}
  -- with (g n (f n vec-xs)) | gf n vec-xs
  -- ... | .vec-xs | refl .vec-xs = {!!}

-- with f n vec-xs | (g n (f n vec-xs)) | gf n vec-xs
--   gf (suc .(length xs)) (x :: vec-xs) | (xs , refl .(length xs)) | .vec-xs | refl .vec-xs = ap (x ::_) {!ap (f (length xs)) (refl vec-xs)!}

-- with (g n (f n vec-xs)) | gf n vec-xs | f n vec-xs
--   gf (suc .(length xs)) (x :: vec-xs) | .vec-xs | refl .vec-xs | (xs , refl .(length xs)) with g (length xs) (xs , refl (length xs))
--   gf (suc .(length xs)) (x :: vec-xs) | .vec-xs | refl .vec-xs | (xs , refl .(length xs)) | f = {!f!}
  --= ap (x ::_) {!!}
    -- where
    --   I : ?
    --   I = g (suc n) (f (suc n) (x :: vec-xs) | f n vec-xs)
  -- = ap ((_::_) x) γ
    -- where
    --   IH : (g n ∘ f n) vec-xs ≡ id vec-xs
    --   IH = gf n vec-xs

    --   γ : (_≡_) {Vector A n} (g n (fst (f n vec-xs) , ap pred (ap suc (snd (f n vec-xs))))) vec-xs
    --   γ = g n (fst (f n vec-xs) , ap pred (ap suc (snd (f n vec-xs)))) ≡⟨ ap (g n) {!Σ-combine (refl (fst (f n vec-xs))) (ap-pred-ap-suc-cancel {_} {_} {snd (f n vec-xs)})!}  ⟩
    --       g n (fst (f n vec-xs) , snd (f n vec-xs)) ≡⟨ ap (g n) (pair-eq (f n vec-xs)) ⟩
    --       g n (f n vec-xs) ≡⟨ IH ⟩
    --       vec-xs ∎

  fg : (n : ℕ) → (f n ∘ g n) ∼ id
  fg zero ([] , refl .zero) = refl ([] , refl zero)
  fg (suc .(length xs)) (x :: xs , refl .(suc (length xs)))
    with
      (f (length xs) ∘ g (length xs)) (xs , refl (length xs))
      | fg (length xs) (xs , refl (length xs))
  fg (suc .(length xs)) (x :: xs , refl .(suc (length xs)))
    | .(xs , refl (length xs))
    | refl .(xs , refl (length xs))
    = refl (x :: xs , refl (suc (length xs)))
  

  f-is-bijection : (n : ℕ) → is-bijection (f n)
  f-is-bijection n = record { inverse = g n ; η = gf n ; ε = fg n }

open _≅_
open is-bijection

test2 : ([ 1 ] , (refl 1)) ≡ (bijection vectors-from-lists) (1 :: [])
test2 = refl (1 :: [] , refl 1)

test3 : (1 :: []) ≡ (inverse (bijectivity vectors-from-lists)) ([ 1 ] , (refl 1))
test3 = refl (1 :: [])

test4 : (2 :: 1 :: []) ≡ (inverse (bijectivity vectors-from-lists)) ((bijection vectors-from-lists) (2 :: 1 :: []))
test4 = refl (2 :: 1 :: [])
```

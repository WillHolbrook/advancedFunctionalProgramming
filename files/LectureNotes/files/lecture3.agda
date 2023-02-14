{-# OPTIONS --without-K --safe #-}

--
--  A list of Agda Emacs Commands can be found here:
--
--    https://agda.readthedocs.io/en/v2.6.3/tools/emacs-mode.html
--
--

module lecture3 where

open import prelude
open import sums

--  Logic with booleans
andB : Bool → Bool → Bool
andB true true = true
andB true false = false
andB false true = false
andB false false = false

orB : Bool → Bool → Bool
orB true true = true
orB true false = true
orB false true = true
orB false false = false

impliesB : Bool → Bool → Bool
impliesB true true = true
impliesB true false = false
impliesB false true = true
impliesB false false = true

-- forallB : (A : Type) (P : A → Bool) → Bool
-- forallB A P = {!!}

-- existsB : (A : Type) (P : A → Bool) → Bool
-- existsB A P = {!!} 

-- Logic with types
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

--
--  Decidable types
--

is-decidable : Type → Type
is-decidable A = A ∔ ¬ A  -- ¬ A := A → 𝟘

-- C-c C-,  -- Show goal and context
-- C-c C-.  -- Show goal and context and current hole's type
-- C-u C-u ... -- Same but first normalize everything
-- C-c C-r  -- Refine

ℕ-is-decidable : is-decidable ℕ
ℕ-is-decidable = inl 4

Bool-is-decidable : is-decidable Bool
Bool-is-decidable = inl true

𝟘-is-decidable : is-decidable 𝟘
𝟘-is-decidable = inr (λ x → x)

𝟙-is-decidable : is-decidable 𝟙
𝟙-is-decidable = inl ⋆

⇔-decidable : {A B : Type} → A ⇔ B → is-decidable A → is-decidable B
⇔-decidable (f , g) (inl a) = inl (f a)
⇔-decidable (f , g) (inr ¬a) = inr (λ b → ¬a (g b))

-- "Classification" of decidable types
false-neq-true : false ≡ true → 𝟘
false-neq-true ()

classify-decidable : (A : Type)
  → is-decidable A
  → Σ b ꞉ Bool , (A ⇔ b ≡ true) 
classify-decidable A (inl a) = true , (λ _ → refl true) , λ _ → a
classify-decidable A (inr ¬a) = false , (λ a → 𝟘-elim (¬a a)) , -- λ { () }
  λ f≡t → 𝟘-elim (false-neq-true f≡t)
  
--
--  Predicates and Relations
--

-- P : A → Bool ~~~~~> P : A → Type

is-decidable-predicate : {A : Type} (P : A → Type) → Type
is-decidable-predicate {A} P = (a : A) → is-decidable (P a) 

-- R : A → A → Bool ~~~~> R : A → A → Type
is-decidable-relation : {A : Type} (R : A → A → Type) → Type
is-decidable-relation {A} R = (a : A) (b : A) → is-decidable (R a b)

--
--  ≤ relation on ℕ 
--

data _≤_ : ℕ → ℕ → Type where
  0≤ : {n : ℕ} → 0 ≤ n
  S≤ : {m n : ℕ} → m ≤ n → suc m ≤ suc n

example : 2 ≤ 4
example = S≤ (S≤ 0≤)

suc-not-≤-zero : {m : ℕ} → suc m ≤ zero → 𝟘
suc-not-≤-zero ()

pred-≤ : {m n : ℕ} → suc m ≤ suc n → m ≤ n
pred-≤ (S≤ m≤n) = m≤n

≤-is-decidable : is-decidable-relation _≤_
≤-is-decidable zero n = inl 0≤
≤-is-decidable (suc m) zero = inr suc-not-≤-zero
≤-is-decidable (suc m) (suc n) = lem (≤-is-decidable m n)

  where lem : is-decidable (m ≤ n) → is-decidable (suc m ≤ suc n)
        lem (inl m≤n) = inl (S≤ m≤n)
        lem (inr m≰n) = inr (λ sm≤sn → m≰n (pred-≤ sm≤sn))

-- C-c C-n -- normalize, i.e run the program
-- ex : Type
-- ex = {!≤-is-decidable 12 4!} 

_≤'_ : ℕ → ℕ → Type
zero ≤' n = 𝟙
suc m ≤' zero = 𝟘
suc m ≤' suc n = m ≤' n

ex2 : 45 ≤' 52
ex2 = ⋆ 

--
inclusion : Bool → Type
inclusion true = 𝟙
inclusion false = 𝟘

_≤''_ : ℕ → ℕ → Bool
zero ≤'' n = true
suc m ≤'' zero = false
suc m ≤'' suc n = m ≤'' n


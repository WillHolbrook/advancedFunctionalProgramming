{-# OPTIONS --without-K --safe #-}

--
--  Attendance Code: 10948947
--

module lecture4 where

open import prelude
open import isomorphisms

--   is-isomorphism : {A B : Type} → (f : A → B) → Type
--   is-isomorphism {A} {B} f = Σ g ꞉ (B → A) , ((g ∘ f ∼ id) × (f ∘ g ∼ id))

--   _≅_ : Type → Type → Type
--   A ≅ B = Σ f ꞉ (A → B) , is-isomorphism f 

-- Example: the identity isomorphism
id-iso : {A : Type} → A ≅ A
id-iso = Isomorphism (λ a → a) (Inverse (λ a → a) (λ a → refl a) (λ a → refl a)) 

Bool-neg : Bool ≅ Bool
Bool-neg = record { bijection = f ; bijectivity = f-is-bijection }
 where
  f : Bool → Bool
  f true = false
  f false = true

  g : Bool → Bool
  g true = false
  g false = true

  gf : g ∘ f ∼ id
  gf true = refl _
  gf false = refl _

  fg : f ∘ g ∼ id
  fg true = refl _
  fg false = refl _

  f-is-bijection : is-bijection f
  f-is-bijection = record { inverse = g ; η = gf ; ε = fg }

-- Example: ∔ is associative
∔-assoc : {A B C : Type} → (A ∔ B) ∔ C ≅ A ∔ (B ∔ C)
∔-assoc {A} {B} {C} = record { bijection = f ; bijectivity = f-is-bijection }
 where
  f : (A ∔ B) ∔ C → A ∔ (B ∔ C)
  f (inl (inl a)) = inl a
  f (inl (inr b)) = inr (inl b)
  f (inr c) = inr (inr c)

  g : A ∔ (B ∔ C) → (A ∔ B) ∔ C
  g (inl a) = inl (inl a)
  g (inr (inl b)) = inl (inr b)
  g (inr (inr c)) = inr c

  gf : g ∘ f ∼ id
  gf (inl (inl a)) = refl _
  gf (inl (inr b)) = refl _
  gf (inr c) = refl _

  fg : f ∘ g ∼ id
  fg (inl a) = refl _
  fg (inr (inl b)) = refl _
  fg (inr (inr c)) = refl _

  f-is-bijection : is-bijection f
  f-is-bijection = record { inverse = g ; η = gf ; ε = fg }

-- Example : Σ and ∔ distribute
Σ-∔-distr : {A : Type} {B C : A → Type}
  → (Σ a ꞉ A , B a ∔ C a) ≅ (Σ a ꞉ A , B a) ∔ (Σ a ꞉ A , C a)
Σ-∔-distr {A} {B} {C}  = record { bijection = f ; bijectivity = f-is-bijection }
 where
  f : Sigma A (λ a → B a ∔ C a) → Sigma A B ∔ Sigma A C
  f (a , inl b) = inl (a , b)
  f (a , inr c) = inr (a , c)

  g : Sigma A B ∔ Sigma A C → Sigma A (λ a → B a ∔ C a)
  g (inl (a , b)) = a , inl b
  g (inr (a , c)) = a , inr c

  gf : g ∘ f ∼ id
  gf (a , inl b) = refl _
  gf (a , inr c) = refl _

  fg : f ∘ g ∼ id
  fg (inl (a , b)) = refl _
  fg (inr (a , c)) = refl _

  f-is-bijection : is-bijection f
  f-is-bijection = record { inverse = g ; η = gf ; ε = fg }

-- Non-example: the constant function is not an isomorphism
not-an-iso : Bool ≅ Bool
not-an-iso = record { bijection = f ; bijectivity = f-is-bijection }
 where
  f : Bool → Bool
  f true = true
  f false = true

  g : Bool → Bool
  g true = true
  g false = false

  gf : g ∘ f ∼ id
  gf true = refl _
  gf false = {!!}

  fg : f ∘ g ∼ id
  fg = {!!}

  f-is-bijection : is-bijection f
  f-is-bijection = record { inverse = g ; η = gf ; ε = fg }

not-an-iso-map : Bool → Bool
not-an-iso-map _ = true

true-is-not-false : true ≡ false → 𝟘
true-is-not-false ()

not-an-iso-map-is-not-an-iso : ¬ (is-bijection not-an-iso-map)
not-an-iso-map-is-not-an-iso is-bij = true-is-not-false (is-bijection.ε is-bij false) 

--
--  Why do we care?
--
--  Answer: anything we can state and prove about a type A, we can also
--  state and prove about any type B which is isomorphic to it.

open is-bijection
open _≅_

trans-pred : {A B : Type} (P : A → Type) (iso : A ≅ B) → (B → Type)
trans-pred P iso b = P (inverse (bijectivity iso) b)

-- transport' : {A : Type} (P : A → Type) {a b : A} (p : a ≡ b) → P a → P b
-- transport' P (refl _) p = p

iso-invariant : {A B : Type} (P : A → Type) (iso : A ≅ B)
  → (a : A) → P a ⇔ trans-pred P iso (bijection iso a)
iso-invariant P iso a = to , from 

  where to : P a → trans-pred P iso (bijection iso a)
        to p = transport P (sym (η (bijectivity iso) a)) p 

        from : trans-pred P iso (bijection iso a) → P a
        from q = transport P (η (bijectivity iso) a) q 

≅-to-⇔ : {A B : Type} → A ≅ B → A ⇔ B
≅-to-⇔ iso = (bijection iso) , inverse (bijectivity iso) 

-- data ℕ' : Type where
--   zero : ℕ'
--   suc : ℕ' → ℕ'

-- A binary representation of the natural numbers
data Bin : Type where
  ⟨⟩ : Bin
  _O : Bin → Bin
  _I : Bin → Bin

infixl 40 _O _I 

thirteen : Bin
thirteen = ⟨⟩ O O O I I O I

suc-Bin : Bin → Bin
suc-Bin ⟨⟩ = ⟨⟩ I 
suc-Bin (b O) = b I
suc-Bin (b I) = (suc-Bin b) O

ℕ-to-Bin : ℕ → Bin
ℕ-to-Bin zero = ⟨⟩
ℕ-to-Bin (suc n) = suc-Bin (ℕ-to-Bin n)

Bin-to-ℕ : Bin → ℕ
Bin-to-ℕ ⟨⟩ = 0
Bin-to-ℕ (b O) = 2 * (Bin-to-ℕ b) 
Bin-to-ℕ (b I) = suc (2 * (Bin-to-ℕ b))

roundtrip-ℕ : (n : ℕ) → Bin-to-ℕ (ℕ-to-Bin n) ≡ n
roundtrip-ℕ zero = refl _
roundtrip-ℕ (suc n) = trans {!!} (ap suc (roundtrip-ℕ n))

roundtrip-Bin : (b : Bin) → ℕ-to-Bin (Bin-to-ℕ b) ≡ b
roundtrip-Bin ⟨⟩ = {!!}
roundtrip-Bin (b O) = {!!}
roundtrip-Bin (b I) = {!!}

num : Bin
num = {!ℕ-to-Bin 4!} 

-- Need to consider only binary representations
-- with *no* extra leading zeros...
reduced : Bin → Type
reduced = {!!} 

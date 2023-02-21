```agda
{-# OPTIONS --without-K --safe #-}

module my-lecture4 where

open import prelude
open import isomorphisms

  -- is-isomorphism : {A B : Type} → (f : A → B) → Type
  -- is-isomorphism {A} {B} f = Σ g ꞉ (B → A) , ((a : A) → g (f a) ≡ a) × ((b : B) → f (g b) ≡ b)

  -- _≅_ : Type → Type → Type
  -- A ≅ B = Σ f ꞉ (A → B) , is-isomorphism f

id-iso : {A : Type} → A ≅ A
id-iso = Isomorphism (λ a → a) (Inverse (λ a → a) refl refl)

Bool-neg : Bool ≅ Bool
Bool-neg = record { bijection = f ; bijectivity = f-is-bijection }
 where
  f : Bool → Bool
  f true = false
  f false = true

  g : Bool → Bool
  g = f

  gf : g ∘ f ∼ id
  gf true = refl true
  gf false = refl false

  fg : f ∘ g ∼ id
  fg true = refl true
  fg false = refl false

  f-is-bijection : is-bijection f
  f-is-bijection = record { inverse = g ; η = gf ; ε = fg }

--Example + is associative (or is associative)
+-assoc : {A B C : Type} → (A ∔ B) ∔ C ≅ A ∔ (B ∔ C)
+-assoc {A} {B} {C} = record { bijection = f ; bijectivity = f-is-bijection }
 where
  f : (A ∔ B) ∔ C →  A ∔ (B ∔ C)
  f (inl (inl a)) = inl a
  f (inl (inr b)) = inr (inl b)
  f (inr c) = inr (inr c)

  g : A ∔ (B ∔ C) → (A ∔ B) ∔ C
  g (inl a) = inl (inl a)
  g (inr (inl b)) = inl (inr b)
  g (inr (inr c)) = inr c

  gf : g ∘ f ∼ id
  gf (inl (inl a)) = refl (inl (inl a))
  gf (inl (inr b)) = refl (inl (inr b))
  gf (inr c) = refl (inr c)

  fg : f ∘ g ∼ id
  fg (inl a) = refl (inl a)
  fg (inr (inl b)) = refl (inr (inl b))
  fg (inr (inr c)) = refl (inr (inr c))

  f-is-bijection : is-bijection f
  f-is-bijection = record { inverse = g ; η = gf ; ε = fg }

-- Σ and ∔ are compatible

Σ-∔-distr : {A : Type} {B C : A → Type} →  (Σ a ꞉ A , B a ∔ C a) ≅ (Σ a ꞉ A , B a) ∔ (Σ a ꞉ A , C a)
Σ-∔-distr {A} {B} {C} = record { bijection = f ; bijectivity = f-is-bijection }
 where
  f : Σ (λ z → B z ∔ C z) → Σ B ∔ Σ C
  f (a , inl ba) = inl (a , ba)
  f (a , inr ca) = inr (a , ca)

  g : Σ B ∔ Σ C → Σ (λ z → B z ∔ C z)
  g (inl (a , ba)) = a , inl ba
  g (inr (a , ca)) = a , inr ca

  gf : g ∘ f ∼ id
  gf (a , inl ba) = refl (a , inl ba)
  gf (a , inr ca) = refl (a , inr ca)

  fg : f ∘ g ∼ id
  fg (inl (a , ba)) = refl (inl (a , ba))
  fg (inr (a , ca)) = refl (inr (a , ca))

  f-is-bijection : is-bijection f
  f-is-bijection = record { inverse = g ; η = gf ; ε = fg }

open is-bijection
open _≅_

trans-pred : {A B : Type} (P : A → Type) (iso : A ≅ B) → (B → Type)
trans-pred P iso b = P (inverse (bijectivity iso) b)

transport' : {A B : Type} (P : A → Type) {a b : A} (p : a ≡ b) → P a → P b
transport' P (refl _) pa = pa

iso-invariant : {A B : Type} (P : A → Type) (iso : A ≅ B) → (a : A) → P a ⇔ trans-pred P iso (bijection iso a)
iso-invariant P iso a = to , from
  where
    to : P a → trans-pred P iso (bijection iso a)
    to pa = transport P (sym (η (bijectivity iso) a)) pa

    from : trans-pred P iso (bijection iso a) → P a
    from q = transport P (η (bijectivity iso) a) q

≅-to-⇔ : {A B : Type} → A ≅ B → A ⇔ B
≅-to-⇔ iso = (bijection iso) , (inverse (bijectivity iso))

data ℕ' : Type where
  ⟨⟩ : ℕ'
  _O : ℕ' → ℕ'
  _I : ℕ' → ℕ'

infixl 50 _O _I

thirteen : ℕ'
thirteen = ⟨⟩ I I O I

suc-ℕ' : ℕ' → ℕ'
suc-ℕ' ⟨⟩ = ⟨⟩ I
suc-ℕ' (n O) = n I
suc-ℕ' (n I) = (suc-ℕ' n) I

ℕ-iso-ℕ' : ℕ ≅ ℕ'
ℕ-iso-ℕ' = record { bijection = f ; bijectivity = f-is-bijection }
 where
  f : ℕ → ℕ'
  f zero = ⟨⟩
  f (suc n) = suc-ℕ' (f n)

  g : ℕ' → ℕ
  g ⟨⟩ = zero
  g (n O) = 2 * (g n)
  g (n I) = suc (2 * (g n)) 

  gf : g ∘ f ∼ id
  gf zero = refl zero
  gf (suc n) = trans {!!} (ap suc (gf n))

  fg : f ∘ g ∼ id
  fg ⟨⟩ = refl ⟨⟩
  fg (n O) = {!!}
  fg (n I) = {!!}

  f-is-bijection : is-bijection f
  f-is-bijection = record { inverse = g ; η = gf ; ε = fg }



```

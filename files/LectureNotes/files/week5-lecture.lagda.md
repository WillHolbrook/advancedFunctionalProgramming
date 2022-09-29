<!--
```agda
open import prelude
open import function-extensionality
open import isomorphisms
open import List-functions hiding (_++_)
open import natural-numbers-functions
open import Vector 
open import Fin

module week5-lecture where
```
-->

```agda

vec-to-fin-map : ∀ {n A} → Vector A n → (k : Fin n) → A
vec-to-fin-map [] ()
vec-to-fin-map (x :: v) zero = x
vec-to-fin-map (x :: v) (suc k) = vec-to-fin-map v k

fin-map-to-vec : ∀ {n A} → (Fin n → A) → Vector A n
fin-map-to-vec {zero} ϕ = []  
fin-map-to-vec {suc n} ϕ = ϕ zero :: fin-map-to-vec (λ k → ϕ (suc k))

vec-round-trip : ∀ {n A} (v : Vector A n)
  → fin-map-to-vec (vec-to-fin-map v) ≡ v
vec-round-trip [] = refl []
vec-round-trip (x :: v) = ap (x ::_) (vec-round-trip v)

postulate

  funext : FunExt

fin-map-round-trip' : ∀ {n A} (ϕ : Fin n → A)
  → vec-to-fin-map (fin-map-to-vec ϕ) ∼ ϕ
fin-map-round-trip' {zero} ϕ ()
fin-map-round-trip' {suc n} ϕ zero = refl (ϕ zero)
fin-map-round-trip' {suc n} ϕ (suc k) = fin-map-round-trip' (λ k → ϕ (suc k)) k

fin-map-round-trip : ∀ {n A} (ϕ : Fin n → A)
  → vec-to-fin-map (fin-map-to-vec ϕ) ≡ ϕ
fin-map-round-trip ϕ = funext (fin-map-round-trip' ϕ) 

vec-fin-map-iso : ∀ {n A} → Vector A n ≅ (Fin n → A)
vec-fin-map-iso {n} {A} = record { bijection = f ; bijectivity = f-is-bijection }
 where
  f : Vector A n → (x : Fin n) → A
  f = vec-to-fin-map

  g : (Fin n → A) → Vector A n
  g = fin-map-to-vec

  gf : g ∘ f ∼ id
  gf = vec-round-trip

  fg : f ∘ g ∼ id
  fg = fin-map-round-trip

  f-is-bijection : is-bijection f
  f-is-bijection = record { inverse = g ; η = gf ; ε = fg }
  
```

```agda

vec-to-list-and-len : ∀ {n A} → Vector A n → (Σ xs ꞉ List A , length xs ≡ n)
vec-to-list-and-len [] = [] , refl zero
vec-to-list-and-len {suc n} {A} (x :: v) = x :: fst ll , ap suc (snd ll)

  where ll : Σ xs ꞉ List A , length xs ≡ n
        ll = vec-to-list-and-len v 

list-and-len-to-vec : ∀ {n A} → (Σ xs ꞉ List A , length xs ≡ n) → Vector A n
list-and-len-to-vec {zero} ([] , refl _) = []
list-and-len-to-vec {suc n} (x :: l , e) = x :: list-and-len-to-vec (l , suc-is-injective e)

suc-is-injective-lem : ∀ {m n} (p : m ≡ n)
  → suc-is-injective (ap suc p) ≡ p
suc-is-injective-lem (refl _) = refl (refl _)

suc-is-injective-lem₁ : ∀ {m n} (p : suc m ≡ suc n)
  → ap suc (suc-is-injective p) ≡ p
suc-is-injective-lem₁ (refl _) = refl (refl _)

vec-there-and-back : ∀ {n A} (v : Vector A n)
  → list-and-len-to-vec (vec-to-list-and-len v) ≡ v
vec-there-and-back [] = refl []
vec-there-and-back {suc n} {A} (x :: v) = ap (x ::_) lem 

  where ll : Σ xs ꞉ List A , length xs ≡ n
        ll = vec-to-list-and-len v 

        lem = list-and-len-to-vec (fst ll , suc-is-injective (ap suc (snd ll)))
                 ≡⟨ ap (λ blnk → list-and-len-to-vec (fst ll , blnk)) (suc-is-injective-lem (snd ll)) ⟩
              list-and-len-to-vec (fst ll , snd ll)                                ≡⟨ vec-there-and-back v ⟩ 
              v ∎ 


list-and-len-there-and-back : ∀ {n A} (ll : Σ xs ꞉ List A , length xs ≡ n)
  → vec-to-list-and-len (list-and-len-to-vec ll) ≡ ll
list-and-len-there-and-back {zero} ([] , refl .zero) = refl ([] , refl zero)
list-and-len-there-and-back {suc n} {A} (x :: l , e) = 

  (x :: fst ll , ap suc (snd ll))           ≡⟨ ap (λ b → x :: fst b , ap suc (snd b)) IH ⟩
  (x :: l , ap suc (suc-is-injective e))    ≡⟨ ap (λ blnk → (x :: l , blnk)) (suc-is-injective-lem₁ e) ⟩ 
  (x :: l , e) ∎ 

  where ll : Σ xs ꞉ List A , length xs ≡ n
        ll = vec-to-list-and-len (list-and-len-to-vec (l , suc-is-injective e))

        IH : (fst ll , snd ll) ≡ (l , suc-is-injective e)
        IH = list-and-len-there-and-back (l , suc-is-injective e)
        
        
vec-list-len-iso : ∀ {n A} → Vector A n ≅ (Σ xs ꞉ List A , length xs ≡ n)
vec-list-len-iso {n} {A} = record { bijection = f ; bijectivity = f-is-bijection }
 where
  f : Vector A n → (Σ xs ꞉ List A , length xs ≡ n)
  f = vec-to-list-and-len

  g : (Σ xs ꞉ List A , length xs ≡ n) → Vector A n
  g = list-and-len-to-vec

  gf : g ∘ f ∼ id
  gf = vec-there-and-back

  fg : f ∘ g ∼ id
  fg = list-and-len-there-and-back

  f-is-bijection : is-bijection f
  f-is-bijection = record { inverse = g ; η = gf ; ε = fg }
```




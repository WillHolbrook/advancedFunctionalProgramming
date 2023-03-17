```agda

module exercises.lab7-solutions where

open import prelude
open import isomorphisms
open import natural-numbers-functions
open import Fin
open import Vector
open import List-functions

×-distributivity-+ : (X Y Z : Type) → (X ∔ Y) × Z ≅ (X × Z) ∔ (Y × Z)
×-distributivity-+ X Y Z =
 record { bijection = f
        ; bijectivity = record { inverse = g
                               ; η       = section
                               ; ε       = retraction } }
  where
   f : (X ∔ Y) × Z → (X × Z) ∔ (Y × Z)
   f (inl x , z) = inl (x , z)
   f (inr y , z) = inr (y , z)

   g : (X × Z) ∔ (Y × Z) → (X ∔ Y) × Z
   g (inl (x , z)) = inl x , z
   g (inr (y , z)) = inr y , z

   section : (g ∘ f) ∼ id
   section (inl x , z) = refl (inl x , z)
   section (inr y , z) = refl (inr y , z)

   retraction : (f ∘ g) ∼ id
   retraction (inl (x , z)) = refl (inl (x , z))
   retraction (inr (y , z)) = refl (inr (y , z))

alternate : Type → Type → Bool → Type
alternate X _ true  = X
alternate _ Y false = Y

∔-isomorphic-to-Σ-bool : (X Y : Type) → (X ∔ Y) ≅ (Σ b ꞉ Bool , alternate X Y b)
∔-isomorphic-to-Σ-bool X Y =
 record { bijection = f ; bijectivity = record { inverse = g
                                               ; η       = section
                                               ; ε       = retraction } }
  where
   f : X ∔ Y → Σ b ꞉ Bool , alternate X Y b
   f (inl x) = true  , x
   f (inr y) = false , y

   g : (Σ b ꞉ Bool , alternate X Y b) → X ∔ Y
   g (true  , X) = inl X
   g (false , Y) = inr Y

   section : (g ∘ f) ∼ id
   section (inl x) = refl (inl x)
   section (inr y) = refl (inr y)

   retraction : (f ∘ g) ∼ id
   retraction (true  , X) = refl (true  , X)
   retraction (false , Y) = refl (false , Y)

sigma-curry-iso : (X Y : Type)
                → (A : X → Y → Type)
                → (Σ x ꞉ X , Σ y ꞉ Y , A x y) ≅ (Σ (x , y) ꞉ X × Y , A x y)
sigma-curry-iso X Y A = record { bijection = f ; bijectivity = f-is-bijection }
 where
  f : Σ x ꞉ X , Σ y ꞉ Y , A x y
    → Σ (x , y) ꞉ X × Y , A x y
  f (x , y , p) = (x , y) , p
  
  g : Σ (x , y) ꞉ X × Y , A x y
    → Σ x ꞉ X , Σ y ꞉ Y , A x y
  g ((x , y) , p) = x , y , p

  gf : g ∘ f ∼ id
  gf (x , y , p) = refl (x , y , p)

  fg : f ∘ g ∼ id
  fg ((x , y) , p) = refl ((x , y) , p)

  f-is-bijection : is-bijection f
  f-is-bijection = record { inverse = g ; η = gf ; ε = fg }

fib : ℕ → ℕ
fib 0 = 0
fib 1 = 1
fib (suc (suc n)) = fib n + fib (suc n)

fib-aux : ℕ → ℕ → ℕ → ℕ
fib-aux a b 0       = b
fib-aux a b (suc n) = fib-aux (b + a) a n

fib-fast : ℕ → ℕ
fib-fast = fib-aux 1 0

fib-aux-fib-lemma : (k n : ℕ) → fib-aux (fib (suc n)) (fib n) k ≡ fib (k + n)
fib-aux-fib-lemma zero    n = refl (fib n)
fib-aux-fib-lemma (suc k) n =
 fib-aux (fib n + fib (1 + n)) (fib (1 + n)) k ≡⟨ refl _              ⟩
 fib-aux (fib (2 + n)) (fib (1 + n)) k         ≡⟨ IH                  ⟩
 fib (k + suc n)                               ≡⟨ ap fib (+-step k n) ⟩
 fib (suc (k + n))                             ∎
 where
  IH : fib-aux (fib (2 + n)) (fib (1 + n)) k ≡ fib (k + suc n)
  IH = fib-aux-fib-lemma k (suc n)

fib-fast-is-correct : (n : ℕ) → fib-fast n ≡ fib n
fib-fast-is-correct n = fib-fast n    ≡⟨ refl _            ⟩
                        fib-aux 1 0 n ≡⟨ claim             ⟩
                        fib (n + 0)   ≡⟨ ap fib (+-base n) ⟩
                        fib n         ∎
 where
  lemma : fib-aux (fib 1) (fib 0) n ≡ fib (n + 0)
  lemma = fib-aux-fib-lemma n 0
  claim : fib-aux 1 0 n ≡ fib (n + 0)
  claim = lemma

data _<_ : ℕ → ℕ → Type where
  zero-<-succ : {n : ℕ} → zero < suc n
  succ-preserves-< : {m n : ℕ} → m < n → suc m < suc n 

_<'_ : ℕ → ℕ → Type
zero <' zero = 𝟘
zero <' suc n = 𝟙
suc m <' zero = 𝟘
suc m <' suc n = m <' n

data is-<-inc : List ℕ → Type where
  []-is-<-inc : is-<-inc []
  n-is-<-inc : (n : ℕ) → is-<-inc (n :: [])
  ::-is-<-inc : {m n : ℕ} (l : List ℕ)
    → is-<-inc (n :: l)
    → m < n
    → is-<-inc (m :: n :: l)

is-<-inc' : List ℕ → Type
is-<-inc' [] = 𝟙
is-<-inc' (x :: []) = 𝟙
is-<-inc' (x :: y :: ns) = (x < y) × is-<-inc' (y :: ns)

data _<-all_ : ℕ → List ℕ → Type where
  <-all-[] : (m : ℕ) → m <-all []
  <-all-:: : (m n : ℕ) (ns : List ℕ)
    → m < n
    → m <-all ns
    → m <-all (n :: ns)

_<-all'_ : (m : ℕ) (l : List ℕ) → Type
m <-all' [] = 𝟙
m <-all' (n :: ns) = (m < n) × (m <-all' ns)

data _all-<_ : List ℕ → ℕ → Type where
  all-<-[] : (n : ℕ) → [] all-< n
  all-<-:: : (m n : ℕ) (ms : List ℕ)
    → m < n 
    → ms all-< n
    → (m :: ms) all-< n 

_all-<'_ : (l : List ℕ) (n : ℕ)  → Type
[] all-<' n = 𝟙
(m :: l) all-<' n = (m < n) × (l all-<' n)


append-<-inc : (n : ℕ) (ns : List ℕ)
  → n <-all ns
  → is-<-inc ns
  → is-<-inc (n :: ns)
append-<-inc n .[] n<ns []-is-<-inc = n-is-<-inc _
append-<-inc n .(m :: []) n<ns (n-is-<-inc m) = {!!}
append-<-inc n .(_ :: _ :: ms) n<ns (::-is-<-inc ms ns-inc x) = {!!}

```

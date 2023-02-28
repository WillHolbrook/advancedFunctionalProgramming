```agda
module exercises.fin where

open import prelude
open import isomorphisms
open import Fin

data _<_ : ℕ → ℕ → Type where
  <-zero : {  y : ℕ} → 0 < suc y
  <-suc : {x y : ℕ} → x < y → suc x < suc y

pred-< : {x y : ℕ} → suc x < suc y → x < y
pred-< {x} {y} (<-suc op) = op

 -- y₀ y₁ y₂ : Fin 3
 -- y₀ = zero {2} -- 0 
 -- y₁ = suc {2} (zero {1}) -- 1
 -- y₂ = suc {2} (suc {1} (zero {0})) -- 2

iso : (n : ℕ) → Fin n ≅ Σ λ k → k < n   
iso n = record { bijection = f n; bijectivity = f-is-bijection n}
 where
  f : (n : ℕ) → Fin n → Σ λ k → k < n
  f (suc n) (zero {n}) = zero , <-zero
  f (suc n) (suc {n} y) = suc (fst IH) , <-suc (snd IH)
    where
      IH : Σ λ k → k < n
      IH = f n y

  g : (n : ℕ) → (Σ λ k → k < n) → Fin n
  g (suc n) (zero , proof) = zero {n}
  g (suc n) (suc witness , proof) = suc {n} (g n (witness , pred-< proof))

  check : g 3 (2 , <-suc {1} {2} (<-suc {zero} {1} (<-zero {zero}))) ≡ suc (suc zero)
  check = refl _ 

  gf : (n : ℕ) → g n ∘ f n ∼ id
  gf (suc n) zero = refl zero
  gf (suc n) (suc comb) = ap suc (gf n comb)

  fg : (n : ℕ) → f n ∘ g n ∼ id
  fg (suc n) (zero , <-zero {.n}) = refl (zero , <-zero {n})
  fg (suc n) (suc witness , <-suc proof)
  -- Reversed arguments - cannot solve
  --with fg n (witness , proof) | (f n ∘ g n) (witness , proof)
  --... | a | b = {!a!}
  -- Correctly ordered arguments, Agda computes
    with (f n ∘ g n) (witness , proof) | fg n (witness , proof)
  ... | .(witness , proof) | refl .(witness , proof) = refl (suc witness , <-suc proof)

  f-is-bijection : (n : ℕ) → is-bijection (f n)
  f-is-bijection n = record { inverse = g n ; η = gf n ; ε = fg n }
```

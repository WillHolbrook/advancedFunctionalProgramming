```agda
module lecture2 where

open import prelude
```
\sum is different to \Sigma but \sigma gives you σ cash money

Following logical expression has the following type in agda
∀x: ℕ.(∃y:ℕ.x = 2*y) ∨ (∃y: ℕ.x = 2y+1)


```agda
odd_or_even_proof : (x : ℕ) → ((Σ y ꞉ ℕ , (x ≡ y * 2)) ∔ (Σ y ꞉ ℕ , (x ≡ y * 2 + 1)))
odd_or_even_proof a = {!!}
--to write ∔ write \dotplus ∔ is used to represent binary sum which is used to represent the either type
--

func : (x : ℕ) → (Σ y ꞉ ℕ , x ≡ x)
func x = (zero , refl x)

func2 : (x : ℕ) → (Σ y ꞉ ℕ , x ≡ x)
func2 x = (zero , refl x)

func3 : (x : ℕ) → (Σ y ꞉ ℕ , x ≡ x)
func3 x = (zero , refl x)
```



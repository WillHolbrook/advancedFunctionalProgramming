# Week 9 - Homework Solutions

```agda
{-# OPTIONS --without-K --safe #-}

module exercises.homework9-solutions where

open import prelude
open import natural-numbers-functions hiding (_≤_)
open import List-functions
open import strict-total-order
open import sorting
open import decidability
open import exercises.lab9-solutions hiding (_≤_)

module _
        {X : Type}
        (sto : StrictTotalOrder X)
       where

 open StrictTotalOrder sto

 _<[Pos]_ : {X : Type} {xs : List X} → Pos xs → Pos xs → Type
 _<[Pos]_ {X} {x :: xs} _       (inl ⋆) = 𝟘
 _<[Pos]_ {X} {x :: xs} (inl ⋆) (inr m) = 𝟙
 _<[Pos]_ {X} {x :: xs} (inr n) (inr m) = n <[Pos] m

 inl-is-not-inr : {Y Z : Type} {y : Y} {z : Z}
                → ¬ (inl {Y} {Z} y ≡ inr {Y} {Z} z)
 inl-is-not-inr ()

 inr-is-not-inl : {Y Z : Type} {y : Y} {z : Z}
                → ¬ (inr {Y} {Z} z ≡ inl {Y} {Z} y)
 inr-is-not-inl ()

 inl-lc : {Y Z : Type} {y₁ y₂ : Y}
        → inl {Y} {Z} y₁ ≡ inl {Y} {Z} y₂ → y₁ ≡ y₂
 inl-lc (refl _) = refl _

 inr-lc : {Y Z : Type} {z₁ z₂ : Z}
        → inr {Y} {Z} z₁ ≡ inr {Y} {Z} z₂ → z₁ ≡ z₂
 inr-lc (refl _) = refl _

 +-has-decidable-equality : {Y Z : Type}
                          → has-decidable-equality Y
                          → has-decidable-equality Z
                          → has-decidable-equality (Y ∔ Z)
 +-has-decidable-equality δy δz (inl y₁) (inl y₂) with δy y₁ y₂
 ... | inl  y₁≡y₂ = inl (ap inl y₁≡y₂)
 ... | inr ¬y₁≡y₂ = inr (λ iy₁≡iy₂ → ¬y₁≡y₂ (inl-lc iy₁≡iy₂))
 +-has-decidable-equality δy δz (inl _ ) (inr _ ) = inr inl-is-not-inr
 +-has-decidable-equality δy δz (inr _ ) (inl _ ) = inr inr-is-not-inl
 +-has-decidable-equality δy δz (inr z₁) (inr z₂) with δz z₁ z₂
 ... | inl  z₁≡z₂ = inl (ap inr z₁≡z₂)
 ... | inr ¬z₁≡z₂ = inr (λ iz₁≡iz₂ → ¬z₁≡z₂ (inr-lc iz₁≡iz₂))

 𝟙-has-decidable-equality : has-decidable-equality 𝟙
 𝟙-has-decidable-equality ⋆ ⋆ = inl (refl ⋆)

 <[Pos]-decidable : {X : Type} {xs : List X}
                  → has-decidable-equality (Pos xs)
 <[Pos]-decidable {X} {x :: xs}
  = +-has-decidable-equality 𝟙-has-decidable-equality <[Pos]-decidable

 <[Pos]-irreflexive : {X : Type} {xs : List X}
                    → (x : Pos xs) → ¬ (x <[Pos] x)
 <[Pos]-irreflexive {X} {x :: xs} (inr n) = <[Pos]-irreflexive n

 <[Pos]-transitive : {X : Type} {xs : List X}
                   → {n m o : Pos xs}
                   → n <[Pos] m → m <[Pos] o → n <[Pos] o
 <[Pos]-transitive {X} {x :: xs} {inl ⋆} {inr m} {inr o} y<z x<z = ⋆
 <[Pos]-transitive {X} {x :: xs} {inr n} {inr m} {inr o} y<z x<z
  = <[Pos]-transitive {X} {xs} {n} {m} {o} y<z x<z

 <[Pos]-connected : {X : Type} {xs : List X}
                  → {n m : Pos xs}
                  → ¬ (n ≡ m) → (n <[Pos] m) ∔ (m <[Pos] n)
 <[Pos]-connected {X} {x :: xs} {inl ⋆} {inl ⋆} ¬in≡im
  = inl (¬in≡im (refl (inl ⋆)))
 <[Pos]-connected {X} {x :: xs} {inl ⋆} {inr _} ¬in≡im = inl ⋆
 <[Pos]-connected {X} {x :: xs} {inr n} {inl ⋆} ¬in≡im = inr ⋆
 <[Pos]-connected {X} {x :: xs} {inr n} {inr m} ¬in≡im
  = <[Pos]-connected (λ n≡m → ¬in≡im (ap inr n≡m))

 STO : (xs : List X) → StrictTotalOrder (Pos xs)
 STO xs = record
          { _<_         = _<[Pos]_
          ; decidable   = <[Pos]-decidable
          ; irreflexive = <[Pos]-irreflexive
          ; transitive  = <[Pos]-transitive {X} {xs}
          ; connected   = <[Pos]-connected
          }

 nsto : NonStrictTotalOrder X
 nsto = non-strict-total-order-from-strict-total-order sto

 NSTO : (xs : List X) → NonStrictTotalOrder (Pos xs)
 NSTO xs = non-strict-total-order-from-strict-total-order (STO xs)

 _≤_ : X → X → Type
 _≤_ = NonStrictTotalOrder._≤_ nsto

 _≤[Pos]_ : {xs : List X} → Pos xs → Pos xs → Type
 _≤[Pos]_ {xs} = NonStrictTotalOrder._≤_ (NSTO xs)

 ≤-reflexive : (x : X) → x ≤ x
 ≤-reflexive = NonStrictTotalOrder.reflexive nsto

 ≤-transitive : {x y z : X} → x ≤ y → y ≤ z → x ≤ z
 ≤-transitive = NonStrictTotalOrder.transitive nsto

 monotonic : {X Y : Type}
           → NonStrictTotalOrder X → NonStrictTotalOrder Y
           → (f : X → Y) → Type
 monotonic {X} {Y} nstox nstoy f = (x y : X) → x ≤X y → f x ≤Y f y
   where
     _≤X_ = NonStrictTotalOrder._≤_ nstox
     _≤Y_ = NonStrictTotalOrder._≤_ nstoy

 tail-sorted : (x : X) (xs : List X)
             → Sorted sto (x :: xs)
             → Sorted sto       xs
 tail-sorted x [] _ = nil-sorted
 tail-sorted x (y :: xs) (adj-sorted s _) = s

 drop-one-sorted : (x y : X) (xs : List X)
                 → Sorted sto (x :: y :: xs)
                 → Sorted sto (x      :: xs)
 drop-one-sorted x y [] (adj-sorted s x≤y) = sing-sorted
 drop-one-sorted x y (z :: xs) (adj-sorted (adj-sorted s y≤z) x≤y)
  = adj-sorted s (≤-transitive x≤y y≤z)

 Inhab-monotonic : (xs : List X) → Sorted sto xs
                   → monotonic (NSTO xs) nsto (Inhab xs)
 Inhab-monotonic (x ::      xs)
                 s
                 n n (inl (refl n))
  = ≤-reflexive (Inhab (x :: xs) n)
 Inhab-monotonic (x :: y :: xs)
                 (adj-sorted s x≤y)
                 (inl ⋆) (inr (inl ⋆)) (inr ⋆)
  = x≤y
 Inhab-monotonic (x :: y :: xs)
                 (adj-sorted s x≤y)
                 (inl ⋆) (inr (inr m)) (inr ⋆)
  = Inhab-monotonic
                 (x ::      xs)
                 (drop-one-sorted x y xs (adj-sorted s x≤y))
                 (inl ⋆) (inr m) (inr ⋆)
 Inhab-monotonic (x :: y :: xs)
                 (adj-sorted s x≤y)
                 (inr n) (inr m) (inr n<m)
  = Inhab-monotonic
                 (     y :: xs)
                 (tail-sorted x (y :: xs) (adj-sorted s x≤y))
                 n m (inr n<m)
```

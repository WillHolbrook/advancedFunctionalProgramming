
# Week 3 Lecture

This file was partially developed before the lecture, partially developed during the lecture, and partially developed after the lecture. This material is also discussed in other handouts.

```agda
{-# OPTIONS --without-K --safe #-}

module week3-lecture where

open import prelude
open import negation
open import natural-numbers-functions


{-

Y : Type  here Y is ℕ
A : Y → Type    for each y : Y, you get a type A y
                here A = λ y → x ≡ 2 * y

Σ y ꞉ Y , A y
An element of this type is a *pair*
                              (y , a)
where y : Y and a : A y

Suppose we define A y = B where B is some type (particular case).

In that case, we abbreviate the Σ type as "Y × B"

-}

is-even is-odd : ℕ → Type
is-even x = Σ y ꞉ ℕ , x ≡ 2 * y
is-odd  x = Σ y ꞉ ℕ , x ≡ 1 + 2 * y

fact-1 : (x : ℕ) → 1 + x ≡ suc x
fact-1 x = refl _

fact-2 : (y : ℕ) → 2 * y ≡ y + y
fact-2 y = refl _

zero-is-even : is-even 0
zero-is-even = 0 , refl 0

ten-is-even : is-even 10
ten-is-even = 5 , refl _

zero-is-not-odd : ¬ is-odd 0    -- is-odd 0 → 𝟘
zero-is-not-odd ()

one-is-not-even : ¬ is-even 1
one-is-not-even (0 , ())
one-is-not-even (suc (suc x) , ())

one-is-not-even' : ¬ is-even 1
one-is-not-even' (suc zero , ())


one-is-odd : is-odd 1
one-is-odd = 0 , refl 1

even-gives-odd-suc' : (x : ℕ) → is-even x → is-odd (suc x)
even-gives-odd-suc' x (y , e) = y , ap suc e
{-
 where
  y' : ℕ
  y' = y

  e' : suc x ≡ suc (2 * y')
  e' = ap suc e

  goal : is-odd (suc x)
  goal = (y' , e')
-}

even-gives-odd-suc : (x : ℕ) → is-even x → is-odd (suc x)
even-gives-odd-suc x (y , e) = goal
 where
  e' : suc x ≡ 1 + 2 * y
  e' = ap suc e

  goal : is-odd (suc x)
  goal = y , e'

fact-3 : (y : ℕ)
       → 2 + 2 * y ≡ 2 * (1 + y)
fact-3 = {!!}

{- how to guess - in general this is an art. But in this casem, it is a science.

we have e : x = 1 + 2 * y
want y' such that suc x = 2 * y'

How do we get y' then?
By e, we have
     suc x = suc (1 + 2 * y)
           = 2 + 2 * y
           = 2 * (1 + y)
           =
-}

odd-gives-even-suc' : (x : ℕ) → is-odd x → is-even (suc x)
odd-gives-even-suc' x (y , e) = goal
 where
  y' : ℕ
  y' = suc y
  e' : suc x ≡ 2 * y'
  e' = suc x           ≡⟨ ap suc e ⟩
       suc (1 + 2 * y) ≡⟨ refl _ ⟩
       2 + 2 * y       ≡⟨ fact-3 y ⟩
       2 * (1 + y)     ≡⟨ refl _ ⟩
       2 * suc y       ≡⟨ refl _ ⟩
       2 * y'          ∎
  goal : is-even (suc x)
  goal = (y' , e')



odd-gives-even-suc : (x : ℕ) → is-odd x → is-even (suc x)
odd-gives-even-suc x (y , e) = goal
 where
  y' : ℕ
  y' = 1 + y

  e' : suc x ≡ 2 * y'
  e' = suc x           ≡⟨ ap suc e ⟩
       suc (1 + 2 * y) ≡⟨ refl _ ⟩
       2 + 2 * y       ≡⟨ fact-3 y ⟩
       2 * (1 + y)     ≡⟨ refl _ ⟩
       2 * y'          ∎

  goal : is-even (suc x)
  goal = y' , e'

even-or-odd : (x : ℕ) → is-even x ∔ is-odd x
even-or-odd 0       = inl (0 , refl 0)
even-or-odd (suc x) = goal
 where
  IH : is-even x ∔ is-odd x
  IH = even-or-odd x

  f : is-even x ∔ is-odd x → is-even (suc x) ∔ is-odd (suc x)
  f (inl e) = inr (even-gives-odd-suc x e)
  f (inr o) = inl (odd-gives-even-suc x o)

  goal : is-even (suc x) ∔ is-odd (suc x)
  goal = f IH
```

We didn't get here in the lecture:

```agda
even : ℕ → Bool
even 0       = true
even (suc x) = not (even x)

even-true  : (y : ℕ)  → even (2 * y) ≡ true
even-true 0       = refl _
even-true (suc y) = even (2 * suc y)         ≡⟨ refl _ ⟩
                    even (suc y + suc y)     ≡⟨ refl _ ⟩
                    even (suc (y + suc y))   ≡⟨ refl _ ⟩
                    not (even (y + suc y))   ≡⟨ ap (not ∘ even) (+-step y y) ⟩
                    not (even (suc (y + y))) ≡⟨ refl _ ⟩
                    not (not (even (y + y))) ≡⟨ not-is-involution (even (y + y)) ⟩
                    even (y + y)             ≡⟨ refl _ ⟩
                    even (2 * y)             ≡⟨ even-true y ⟩
                    true ∎

even-false : (y : ℕ) → even (1 + 2 * y) ≡ false
even-false 0       = refl _
even-false (suc y) = even (1 + 2 * suc y)   ≡⟨ refl _ ⟩
                     even (suc (2 * suc y)) ≡⟨ refl _ ⟩
                     not (even (2 * suc y)) ≡⟨ ap not (even-true (suc y)) ⟩
                     not true               ≡⟨ refl _ ⟩
                     false                  ∎
```

Done after the lecture:

```agda
div-by-2 : ℕ → ℕ
div-by-2 x = f (even-or-odd x)
 where
  f : is-even x ∔ is-odd x → ℕ
  f (inl (y , _)) = y
  f (inr (y , _)) = y

open import natural-numbers-functions

even-odd-lemma : (y z : ℕ) →  1 + 2 * y ≡ 2 * z → 𝟘
even-odd-lemma y z e = false-is-not-true impossible
 where
  impossible = false            ≡⟨ sym (even-false y) ⟩
               even (1 + 2 * y) ≡⟨ ap even e ⟩
               even (2 * z)     ≡⟨ even-true z ⟩
               true             ∎

not-both-even-and-odd : (x : ℕ) → ¬ (is-even x × is-odd x)
not-both-even-and-odd x ((y , e) , (y' , o)) = even-odd-lemma y' y d
 where
  d = 1 + 2 * y' ≡⟨ sym o ⟩
      x          ≡⟨ e ⟩
      2 * y      ∎
```

exercises

```agda
double : ℕ → ℕ
double 0 = 0
double (suc x) = suc (suc (double x))

double-correct : (x : ℕ) → double x ≡ x + x
double-correct 0       = double 0 ≡⟨ refl _ ⟩
                         0        ≡⟨ refl _ ⟩
                         0 + 0    ∎
double-correct (suc x) = goal
 where
  IH : double x ≡ x + x
  IH = double-correct x

  goal : double (suc x) ≡ suc x + suc x
  goal = double (suc x)       ≡⟨ refl _ ⟩
         suc (suc (double x)) ≡⟨ ap (suc ∘ suc) IH ⟩
         suc (suc (x + x))    ≡⟨ ap suc (sym (+-step x x)) ⟩
         suc (x + suc x)      ≡⟨ refl _ ⟩
         suc x + suc x        ∎

```

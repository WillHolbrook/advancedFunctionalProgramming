```agda
{-# OPTIONS --without-K --safe #-}

module exercises.lab4-solutions where

open import prelude
open import List-functions

private

 reverse-lemma : {X : Type} (x : X) (xs : List X)
               → x :: reverse xs ≡ reverse (xs ++ [ x ])
 reverse-lemma x []        = refl (x :: [])
 reverse-lemma x (y :: xs) = ap (_++ [ y ]) (reverse-lemma x xs)

 reverse-is-involution : {X : Type} → (xs : List X) → xs ≡ reverse (reverse xs)
 reverse-is-involution {X} [] = refl []
 reverse-is-involution {X} (x :: xs)
  = x :: xs                       ≡⟨ ap (x ::_) (reverse-is-involution xs) ⟩
    x :: reverse (reverse xs)     ≡⟨ reverse-lemma x (reverse xs)          ⟩
    reverse (reverse xs ++ [ x ]) ≡⟨ refl (reverse (reverse xs ++ [ x ]))  ⟩
    reverse (reverse (x :: xs))   ∎

+-assoc : (x y z : ℕ) → x + (y + z) ≡ (x + y) + z
+-assoc zero    y z = refl (y + z)
+-assoc (suc x) y z = ap suc (+-assoc x y z)


data _≤_ : ℕ → ℕ → Type where
  ≤-zero : (  y : ℕ) → 0 ≤ y
  ≤-suc  : (x y : ℕ) → x ≤ y → suc x ≤ suc y

_≤'_ : ℕ → ℕ → Type
x ≤' y = Σ k ꞉ ℕ , x + k ≡ y


≤'-zero : (y : ℕ) → 0 ≤' y
≤'-zero y = y , refl y

≤'-suc : (x y : ℕ) → x ≤' y → suc x ≤' suc y
≤'-suc x y (n , p) = n , ap suc p

≤-prime : (x y : ℕ) → x ≤ y → x ≤' y
≤-prime 0            y  (≤-zero  y)   = ≤'-zero y
≤-prime (suc x) (suc y) (≤-suc x y p) = ≤'-suc x y (≤-prime x y p)

≤-unprime : (x y : ℕ) → x ≤' y → x ≤ y
≤-unprime zero y (n , p)
 = ≤-zero y
≤-unprime (suc x) (suc .(x + n)) (n , refl .(suc (x + n)))
 = ≤-suc x (x + n) (≤-unprime x (x + n) (n , refl (x + n)))

≤-trans : (x y z : ℕ) → x ≤ y → y ≤ z → x ≤ z
≤-trans zero y z p q
 = ≤-zero z
≤-trans (suc x) .(suc y) .(suc z) (≤-suc .x y p) (≤-suc .y z q)
 = ≤-suc x z (≤-trans x y z p q)

≤'-trans : (x y z : ℕ) → x ≤' y → y ≤' z → x ≤' z
≤'-trans x .(x + n) .((x + n) + m) (n , refl .(x + n)) (m , refl .((x + n) + m))
 = (n + m) , +-assoc x n m

private

 is-decidable : Type → Type
 is-decidable A = A ∔ ¬ A

 has-decidable-equality : Type → Type
 has-decidable-equality A = (x y : A) → is-decidable (x ≡ y)

 bool-has-decidable-equality : has-decidable-equality Bool
 bool-has-decidable-equality true  true  = inl (refl true)
 bool-has-decidable-equality true  false = inr (λ ())
 bool-has-decidable-equality false true  = inr (λ ())
 bool-has-decidable-equality false false = inl (refl false)

 ≤-lemma : (m n : ℕ) → suc m ≤ suc n → m ≤ n
 ≤-lemma m n (≤-suc m n p) = p

 not-suc-≤-zero : (n : ℕ) → ¬ (suc n ≤ 0)
 not-suc-≤-zero n ()

 ≤-is-decidable : (m n : ℕ) → is-decidable (m ≤ n)
 ≤-is-decidable zero    zero    = inl (≤-zero zero)
 ≤-is-decidable zero    (suc n) = inl (≤-zero (suc n))
 ≤-is-decidable (suc m) zero    = inr (not-suc-≤-zero m)
 ≤-is-decidable (suc m) (suc n) = ∔-nondep-elim f g IH
  where
   IH : (m ≤ n) ∔ ¬ (m ≤ n)
   IH = ≤-is-decidable m n
   f : m ≤ n → is-decidable (suc m ≤ suc n)
   f p = inl (≤-suc m n p)
   g : ¬ (m ≤ n) → is-decidable (suc m ≤ suc n)
   g p = inr (λ q → p (≤-lemma m n q))

is-decidable-predicate : {X : Type} → (X → Type) → Type
is-decidable-predicate {X} A = (x : X) → is-decidable (A x)

is-exhaustively-searchable : Type → Type₁
is-exhaustively-searchable X = (A : X → Type)
                             → is-decidable-predicate A
                             → is-decidable (Σ x ꞉ X , A x)

data Fin : ℕ → Type where
  zero : {n : ℕ} → Fin (suc n)
  succ : {n : ℕ} → Fin n → Fin (suc n)

Fin-search-base : is-exhaustively-searchable (Fin 0)
Fin-search-base A d = inr n
 where
  n : ¬ (Σ x ꞉ Fin 0 , A x)
  n ((), _)

{-

In the following, we could have used ∔-elim, but instead we are using
(equivalently) helper functions II and IV which do pattern matching
on their input to check which case holds. We are doing this for the
sake of clarity. In particular, this allows us to see the types of the
subterms.

The idea of the function is to check whether A zero holds or not using
the assumption that it is decidable, here called d. If it holds, we
are done: we've found what we are looking for. Otherwise, we use the
searcher s to check whether there is x with A (succ x) in III.

-}

Fin-search-step : (n : ℕ)
                → is-exhaustively-searchable (Fin n)
                → is-exhaustively-searchable (Fin (suc n))
Fin-search-step n s = I
 where
  I : is-exhaustively-searchable (Fin (suc n))
  I A d = II (d zero) -- Check whether A zero holds using g and feeds this to II.
   where
    II : A zero ∔ ¬ A zero → is-decidable (Σ x ꞉ Fin (suc n) , A x)
    II (inl a) = inl (zero , a) -- We have that a : A zero, so we've found something.
    II (inr f) = IV III         -- f says that ¬ A zero.
                                -- So search after zero using s with III,
                                -- And then feed this to IV to see whether we got
                                -- something or not.
     where
      III : is-decidable (Σ x ꞉ Fin n , A (succ x))
      III = s (λ x → A (succ x)) (λ x → d (succ x))

      IV : is-decidable (Σ x ꞉ Fin n , A (succ x))
         → is-decidable (Σ x ꞉ Fin (suc n) , A x)
      IV (inl (x , a)) = inl (succ x , a) -- We've found something.
      IV (inr g)       = inr V            -- g says that ¬ (Σ x ꞉ Fin (succ n) , A (succ x)),
                                          -- so there is nothing to be found, which is
                                          -- proved by V with two cases, using f and g.
       where
        V : ¬ (Σ x ꞉ Fin (suc n) , A x)
        V (zero   , a) = f a
        V (succ x , a) = g (x , a)

Fin-is-exhaustively-searchable : (n : ℕ) → is-exhaustively-searchable (Fin n)
Fin-is-exhaustively-searchable 0       = Fin-search-base
Fin-is-exhaustively-searchable (suc n) = Fin-search-step n (Fin-is-exhaustively-searchable n)

-- Examples

A : Fin 5 → Type
A zero = 𝟘
A (succ zero) = 𝟘
A (succ (succ zero)) = 𝟙
A (succ (succ (succ x))) = 𝟘

𝟘-is-decidable : is-decidable 𝟘
𝟘-is-decidable = inr id

𝟙-is-decidable : is-decidable 𝟙
𝟙-is-decidable = inl ⋆

A-is-decidable : (x : Fin 5) → is-decidable (A x)
A-is-decidable zero = 𝟘-is-decidable
A-is-decidable (succ zero) = 𝟘-is-decidable
A-is-decidable (succ (succ zero)) = 𝟙-is-decidable
A-is-decidable (succ (succ (succ x))) = 𝟘-is-decidable

example-A : Fin-is-exhaustively-searchable 5 A A-is-decidable ≡ inl (succ (succ zero) , ⋆)
example-A = refl _

B : Fin 4 → Type
B x = 𝟘

B-is-decidable : (x : Fin 4) → is-decidable (B x)
B-is-decidable _ = 𝟘-is-decidable

example-B : Fin-is-exhaustively-searchable 4 B B-is-decidable ≡ inr _
example-B = refl _

# Lab 7 - Lab Exercises

```agda
module exercises.my-lab7v2 where

open import prelude
open import isomorphisms
open import natural-numbers-functions
open import Fin
open import Vector
open import List-functions
```

## Part I: Isomorphisms

### Exercise 1.1

**Prove** the following isomorphism:

```agda
×-distributivity-+ : (X Y Z : Type) → (X ∔ Y) × Z ≅ (X × Z) ∔ (Y × Z)
×-distributivity-+ X Y Z = record { bijection = f ; bijectivity = f-is-bijection }
 where
  f : (X ∔ Y) × Z → (X × Z) ∔ (Y × Z)
  f (inl x , z) = inl (x , z)
  f (inr y , z) = inr (y , z)

  g : (X × Z) ∔ (Y × Z) → (X ∔ Y) × Z
  g (inl (x , z)) = inl x , z
  g (inr (y , z)) = inr y , z

  gf : g ∘ f ∼ id
  gf (inl x , z) = refl (inl x , z)
  gf (inr y , z) = refl (inr y , z)

  fg : f ∘ g ∼ id
  fg (inl (x , z)) = refl (inl (x , z))
  fg (inr (y , z)) = refl (inr (y , z))

  f-is-bijection : is-bijection f
  f-is-bijection = record { inverse = g ; η = gf ; ε = fg }

```

### Exercise 1.2

We now define a function `alternate` that takes two types `X` and `Y` and
evaluates to `X` on `true` and evaluates to `Y` on `false`.

```agda
alternate : Type → Type → Bool → Type
alternate X _ true  = X
alternate _ Y false = Y
```

It can be proved that `Σ b ꞉ Bool , alternate X Y b` is the same thing as `X ∔
Y`. **Prove** this by constructing the following isomorphism:

```agda
∔-isomorphic-to-Σ-bool : (X Y : Type) → (X ∔ Y) ≅ (Σ b ꞉ Bool , alternate X Y b)
∔-isomorphic-to-Σ-bool X Y = record { bijection = f ; bijectivity = f-is-bijection }
 where
  f : X ∔ Y → Σ b ꞉ Bool , alternate X Y b
  f (inl x) = true , x
  f (inr y) = false , y

  g : (Σ b ꞉ Bool , alternate X Y b) → X ∔ Y
  g (true  , x) = inl x
  g (false , y) = inr y

  gf : g ∘ f ∼ id
  gf (inl x) = refl (inl x)
  gf (inr y) = refl (inr y)

  fg : f ∘ g ∼ id
  fg (true  , x) = refl (true , x)
  fg (false , y) = refl (false , y)

  f-is-bijection : is-bijection f
  f-is-bijection = record { inverse = g ; η = gf ; ε = fg }
```

### Exercise 1.3

**Prove** the following isomorphism:

```agda
sigma-curry-iso : (X Y : Type)
                → (A : X → Y → Type)
                → (Σ x ꞉ X , Σ y ꞉ Y , A x y) ≅ (Σ (x , y) ꞉ X × Y , A x y)
sigma-curry-iso X Y A = record { bijection = f ; bijectivity = f-is-bijection }
 where
  f : (Σ x ꞉ X , Σ y ꞉ Y , A x y) → Σ (x , y) ꞉ X × Y , A x y
  f (x , y , axy) = (x , y) , axy

  g : (Σ (x , y) ꞉ X × Y , A x y) → Σ x ꞉ X , Σ y ꞉ Y , A x y
  g ((x , y) , axy) = x , y , axy

  gf : g ∘ f ∼ id
  gf (x , y , axy) = refl (x , y , axy)

  fg : f ∘ g ∼ id
  fg ((x , y) , axy) = refl ((x , y) , axy)

  f-is-bijection : is-bijection f
  f-is-bijection = record { inverse = g ; η = gf ; ε = fg }

```

## Part II: Proving correctness of efficient Fibonacci

In Functional Programming you saw two ways of defining the Fibonacci function.
The first one, `fib` was fairly simple, but inefficient

```agda
fib : ℕ → ℕ
fib 0             = 0
fib 1             = 1
fib (suc (suc n)) = fib n + fib (suc n)
```

Therefore, we introduce a second version, `fib-fast`, which uses an accumulating
parameter to make it more efficient.

```agda
fib-aux : ℕ → ℕ → ℕ → ℕ
fib-aux a b 0       = b
fib-aux a b (suc n) = fib-aux (b + a) a n

fib-fast : ℕ → ℕ
fib-fast = fib-aux 1 0
```

It is not obvious, however, that `fib-fast` implements the same behaviour as
`fib`. In Agda, we can *prove* this, showing that `fib-fast` is correct.

The following lemma relates `fib-aux` and `fib` and is fundamental in proving
the correctness of `fib-fast`. You will be asked to prove it later.

```agda
fib-aux-fib-lemma : (k n : ℕ) → fib-aux (fib (suc n)) (fib n) k ≡ fib (k + n)
fib-aux-fib-lemma zero n = refl (fib n)
fib-aux-fib-lemma (suc k) n = 
   fib-aux (fib n + fib (suc n)) (fib (suc n)) k ≡⟨ fib-aux-fib-lemma k (suc n) ⟩
   fib (k + suc n)                               ≡⟨ ap fib (+-step k n) ⟩
   fib (suc (k + n))                             ∎
```

### Exercise 2.1

Using `fib-aux-fib-lemma`, **prove** the correctness of `fib-fast`.

```agda
fib-fast-is-correct : (n : ℕ) → fib-fast n ≡ fib n
fib-fast-is-correct n = 
   fib-aux 1 0 n ≡⟨ fib-aux-fib-lemma n zero ⟩
   fib (n + zero) ≡⟨ ap fib (+-base n) ⟩
   fib n ∎
```

*Hints*:
1. The lemma allows you to prove this fairly directly. There is no need to do
induction on `n`.
1. You may also find the `+-base` function from the
[natural-numbers-functions](../natural-numbers-functions.lagda.md) module useful.

### Exercise 2.2

Now **complete** the proof of fundamental lemma `fib-aux-fib-lemma` above.

*Hint*: You will probably want to use `+-step` from
[natural-numbers-functions](../natural-numbers-functions.lagda.md) at some
point.

### References

The exercises and solutions of Part 2 were based on [Neil Mitchell's
proof][mitchell] in the programming language [Idris][idris].

[mitchell]: http://neilmitchell.blogspot.com/2017/05/proving-fib-equivalence.html
[idris]: https://en.wikipedia.org/wiki/Idris_(programming_language)

## Part III: Inductive and Recursive Predicates and Relations

In the following sequence of exercises, we will practice writing
predicates and relations both inductively and recursively.

### Exercise 3.1

Define the strict order relation (i.e. m < n) on the natural numbers.
Do this both as an inductive predicate by adding constructors to the
following skeleton:

```agda
data _<_ : ℕ → ℕ → Type where
 <-zero : (n : ℕ) → 0 < suc n
 <-suc : (n m : ℕ) → n < m → suc n < suc m
```

and now as a recursive definition:

```agda
_<'_ : ℕ → ℕ → Type
n     <' zero  = 𝟘
zero  <' suc m = 𝟙
suc n <' suc m = n <' m
```

### Exercise 3.2

Define a predicate `is-<-inc` on lists of natural numbers which states
that adjacent elements of the list are strictly increasing.  That is,
we should be able to prove `is-<-inc (2 :: 4 :: 7 :: [])` but *not*
`is-<-inc (4 :: 2 :: 7 [])`.  Do this both as an inductive and recursive
definition:

```agda
data is-<-inc : List ℕ → Type where
  nil-sorted  : is-<-inc []
  sing-sorted : (n : ℕ) → is-<-inc (n :: [])
  ::-sorted   : (n m : ℕ)(ms : List ℕ) → is-<-inc (m :: ms) → n < m → is-<-inc (n :: m :: ms)

is-<-inc' : List ℕ → Type
is-<-inc' [] = 𝟙
is-<-inc' (x :: []) = 𝟙
is-<-inc' (x :: y :: xs) = x < y × is-<-inc' (y :: xs)
```

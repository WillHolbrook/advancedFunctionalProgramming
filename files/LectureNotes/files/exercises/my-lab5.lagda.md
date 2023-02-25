# Week 5 - Lab Sheet

```agda
{-# OPTIONS --without-K --safe #-}

module exercises.my-lab5 where

private
 open import prelude
 open import natural-numbers-functions hiding (_≤_ ; is-even ; is-odd ; +-comm)
 open import List-functions
 open import isomorphisms
```

We will also want to use some things from the Lab and Homework sheet of Week 4:

```agda
 open import exercises.homework4-solutions
 open import exercises.lab4-solutions
```

## Part I: Length

In the file [List-functions.lagda.md](../List-functions.lagda.md), the
function `length` is recursively defined as follows.

```agdacode
length : {A : Type} → List A → ℕ
length []        = 0
length (x :: xs) = 1 + length xs
```

In the following exercises we will prove some facts involving the length of
lists. In doing so, you will practise with inductive proofs.

### Exercise 1.1

Recall that we defined `map` as follows (see
[List-functions.lagda.md](../List-functions.lagda.md)).

```agdacode
map : {A B : Type} → (A → B) → List A → List B
map f []        = []
map f (x :: xs) = f x :: map f xs
```

**Prove** that `map` preserves the length of a list.

```agda
 map-preserves-length : {A B : Type} (f : A → B) (xs : List A)
                      → length (map f xs) ≡ length xs
 map-preserves-length f [] = refl zero
 map-preserves-length f (x :: xs) = ap suc (map-preserves-length f xs)
```

### Exercise 1.2

Another useful fact is that the length of two concatenated lists is the sum of
their respective lengths. **Complete** the proof of this fact.

```agda
 length-of-++ : {A : Type} (xs ys : List A)
              → length (xs ++ ys) ≡ length xs + length ys
 length-of-++ [] ys = refl _
 length-of-++ (x :: xs) ys = ap suc (length-of-++ xs ys)
```

### Exercise 1.3

Recall `≤'` from Lab Sheet 4 and `≼'` from Homework Sheet 4

```agdacode
_≤'_ : ℕ → ℕ → Type
x ≤' y = Σ k ꞉ ℕ , x + k ≡ y
```

```agdacode
_≼'_ : {X : Type} → List X → List X → Type
_≼'_ {X} xs ys = Σ zs ꞉ List X , xs ++ zs ≡ ys
```

and that `x ≤' y` expresses that the natural number `x` is less than or equal to
the natural number `y`, while `xs ≼' ys` expresses that the list `xs` is a
prefix of the list `ys`.

**Prove** that the length of a prefix of a list `ys` is less than the length of
`ys`, relating the two notions above.

```agda
 pop-list : {A : Type} → List A → List A
 pop-list [] = []
 pop-list (x :: xs) = xs
 
 ≼'-cons : {X : Type} (x : X) (xs ys : List X)
         → xs ≼' ys
         → (x :: xs) ≼' (x :: ys)
 ≼'-cons x xs ys (zs , e) = (zs , ap (λ - → x :: -) e)

--Above Two Functions Aren't used
 
 length-of-prefix : {A : Type} (xs ys : List A)
                  → xs ≼' ys
                  → length xs ≤' length ys
 length-of-prefix [] ys (tail , prf) = (length ys) , (refl (length ys))
 length-of-prefix (x :: xs) (.x :: .(xs ++ tail)) (tail , refl .(x :: xs ++ tail)) = ≤'-suc (length xs) (length (xs ++ tail)) IH
   where
     IH : length xs ≤' length (xs ++ tail)
     IH = length-of-prefix xs (xs ++ tail) (tail , (refl (xs ++ tail)))
```

### Exercise 1.4

A nice use case of the length function is that we are now able to define safe
`head` and `tail` operations on nonempty lists.

We say that a list is *nonempty* if its length is at least 1.
```agda
 is-nonempty : {A : Type} → List A → Type
 is-nonempty xs = 1 ≤' length xs
```

We can then define `tail` as follows.
```agda
 tail : {A : Type} (xs : List A) → is-nonempty xs → List A
 tail (x :: xs) p = xs
```

Agda accepts this definition and does not complain about missing the `[]`-case,
because it realizes that `[]` does not satisfy `is-nonempty`.

#### Exercise 1.4a

```agda
 head : {A : Type} (xs : List A) → is-nonempty xs → A
 head (x :: xs) p = x
```

**Complete** the definition of `head` yourself.

#### Exercise 1.4b

```agda
 length-of-tail : {A : Type} (xs : List A) (p : 1 ≤' length xs)
                → 1 + length (tail xs p) ≡ length xs
 length-of-tail (x :: xs) p = ap suc (refl (length xs))

 --This can be re-written with the definition of `is-nonempty xs` as follows
 length-of-tail' : {A : Type} (xs : List A) (p : is-nonempty xs)
                 → 1 + length (tail xs p) ≡ length xs
 length-of-tail' (x :: xs) p = ap suc (refl (length xs))
 
```

**Prove** that the length of a list is obtained by adding 1 to the length of the
tail.

#### Exercise 1.4c

```agda
 ≤'-suc-lemma : (n : ℕ) → n ≤' (1 + n)
 ≤'-suc-lemma zero = 1 , (refl 1)
 ≤'-suc-lemma (suc n) = ≤'-suc n (1 + n) IH
   where
     IH : n ≤' (1 + n)
     IH = ≤'-suc-lemma n

 length-of-tail-decreases : {A : Type} (xs : List A) (p : 1 ≤' length xs)
                          → length (tail xs p) ≤' length xs
 length-of-tail-decreases (x :: xs) p = ≤'-suc-lemma (length xs)
```

**Complete** the proof of the following lemma and use it to prove that the
length of the tail of a list is less than the length of the full list.

## Part II: Isomorphisms

Make sure you have read the [file on isomorphisms](../isomorphisms.lagda.md),
where we define ismorphisms and show that `Bool ≅ 𝟚`.

You will now give three more isomorphisms. In each case, you should think
about *why* and *how* each pair of types are isomorphic before attemping to
formalise the isomorphism.

### Exercise 2.1

```agda
 ×-iso : (X Y : Type) → X × Y ≅ Y × X
 ×-iso X Y = record { bijection = f ; bijectivity = f-is-bijection }
  where
   f : X × Y → Y × X
   f (x , y) = y , x

   g : Y × X → X × Y
   g (y , x) = x , y

   gf : g ∘ f ∼ id
   gf (y , x) = refl (y , x)

   fg : f ∘ g ∼ id
   fg (x , y) = refl (x , y)

   f-is-bijection : is-bijection f
   f-is-bijection = record { inverse = g ; η = gf ; ε = fg }
```

**Show** that X × Y is isomorphic to Y × X using the above template.

### Exercise 2.2

```agda
 +-iso : (X Y : Type) → X ∔ Y ≅ Y ∔ X
 +-iso X Y = record { bijection = f ; bijectivity = f-is-bijection }
  where
   f : X ∔ Y → Y ∔ X
   f (inl x) = inr x
   f (inr y) = inl y

   g : Y ∔ X → X ∔ Y
   g (inl y) = inr y
   g (inr x) = inl x

   gf : g ∘ f ∼ id
   gf (inl x) = refl (inl x)
   gf (inr y) = refl (inr y)

   fg : f ∘ g ∼ id
   fg (inl y) = refl (inl y)
   fg (inr x) = refl (inr x)

   f-is-bijection : is-bijection f
   f-is-bijection = record { inverse = g ; η = gf ; ε = fg }
```

### Exercise 2.3

```agda
 vec-suc : {A : Type} (a : A) (n : ℕ) → Vector A n → Σ n₁ ꞉ ℕ , Vector A (suc n)
 vec-suc a n vec = (suc n) , (a :: vec)

 lists-from-vectors : {A : Type} → List A ≅ (Σ n ꞉ ℕ , Vector A n)
 lists-from-vectors {A}
  = record { bijection = f ; bijectivity = f-is-bijection }
  where
   f : List A → Σ n ꞉ ℕ , Vector A n
   f [] = zero , []
   f (x :: xs) with f xs
   ... | n , vec-xs = suc n , x :: vec-xs
   -- (suc (fst (f xs)) , x :: (snd (f xs)))
--with f xs
-- ... | n , vec-xs = (suc n) , (x :: vec-xs)

   g : Σ n ꞉ ℕ , Vector A n → List A
   g (zero , []) = []
   g (suc n , x :: vec-xs) = x :: (g (n , vec-xs))

   gf : g ∘ f ∼ id
   gf [] = refl []
   gf (x :: xs) = ap (_::_ x) (gf xs)

   fg : f ∘ g ∼ id
   fg (zero , []) = refl (zero , [])
   fg (suc n , x :: vec-xs) with (f ∘ g) (n , vec-xs) | fg (n , vec-xs)
   ... | .n , .vec-xs | refl .(n , vec-xs) = refl (suc n , x :: vec-xs)

   f-is-bijection : is-bijection f
   f-is-bijection = record { inverse = g ; η = gf ; ε = fg }
```
Inspired from (here)[https://lists.chalmers.se/pipermail/agda/2014/006892.html]

**Show** that the the type `List A` is isomorphic to the type `Σ (Vector A)`.

(Note that this is the first question in [this question
sheet](../vector-and-list-isomorphisms.lagda.md)).

Hint: The statement of Exercise 2.3b may help you.

### Exercise 2.3b

```agda
 open _≅_

 lfv-preserves-length : {A : Type} (xs : List A)
                      → fst (bijection lists-from-vectors xs)
                      ≡ length xs
 lfv-preserves-length [] = refl zero
 lfv-preserves-length (x :: xs) = ap suc (lfv-preserves-length xs)
```

Notice how `bijection` extracts the function `f` you defined in
`lists-from-vectors`.

**Prove** that for any `xs : List A`, the length of `xs` is the same as the
first projection of `f xs : Σ (Vector A)` (where `f : ℕ → List 𝟙` is as you
defined in Exercise 4a).

## Part III: Evenness

In the lecture notes, you have seen the predicates `is-even` and `is-odd`:

```agda
 is-even is-odd : ℕ → Type
 is-even x = Σ y ꞉ ℕ , x ≡ 2 * y
 is-odd  x = Σ y ꞉ ℕ , x ≡ 1 + 2 * y
```

In these exercises, we will define a Boolean-valued version of the `is-even`
predicate and prove that the two versions are _logically_ equivalent:

```agda
 check-even : ℕ → Bool
 check-even zero          = true
 check-even (suc zero)    = false
 check-even (suc (suc n)) = check-even n
```

### Exercise 3.1

First, we will have to prove two lemmas that we will use in Exercise 3.2, where
we will prove our main result.

```agda
 +-suc-on-right : (x y : ℕ) → x + suc y ≡ suc (x + y)
 +-suc-on-right 0       y = refl (suc y)
 +-suc-on-right (suc x) y = ap suc (+-suc-on-right x y)

 evenness-lemma₁ : (n : ℕ) → is-even (2 + n) → is-even n
 evenness-lemma₁ n (suc k , p) = k , goal
  where
   subgoal : suc (suc n) ≡ suc (suc (2 * k))
   subgoal = suc (suc n)       ≡⟨ p ⟩
             suc k + suc k     ≡⟨ ap suc (+-suc-on-right k k) ⟩
             suc ((suc k) + k) ∎

   goal : n ≡ 2 * k
   goal = suc-is-injective (suc-is-injective subgoal)

 evenness-lemma₂ : (n : ℕ) → is-even n → is-even (2 + n)
 evenness-lemma₂ n (k , p) = suc k , goal
  where
   goal : 2 + n ≡ 2 * suc k
   goal = 2 + n         ≡⟨ ap (suc ∘ suc) p ⟩
          2 + (k + k)   ≡⟨ ap suc (sym (+-suc-on-right k k)) ⟩
          suc k + suc k ∎
```

**Complete** the above proofs.

### Exercise 3.2

**Prove** that if `is-even n` is inhabited, then `check-even n ≡ true`.

```agda
 not-1≡suc-suc : (n : ℕ) → ¬(1 ≡ suc (n + suc n))
 not-1≡suc-suc zero ()
 not-1≡suc-suc (suc n) ()

 even⇒check-even : (n : ℕ) → is-even n → check-even n ≡ true
 even⇒check-even zero e = refl true
 even⇒check-even (suc zero) (suc n/2 , prf) = 𝟘-elim (not-1≡suc-suc n/2 prf)
 even⇒check-even (suc (suc n)) e = even⇒check-even n (evenness-lemma₁ n e)
```

**Prove** that if `check-even n ≡ true` then `is-even n` is inhabited:

```agda
 check-even⇒even : (n : ℕ) → check-even n ≡ true → is-even n
 check-even⇒even zero prf = zero , refl zero
 check-even⇒even (suc (suc n)) prf = evenness-lemma₂ n (check-even⇒even n prf)
```

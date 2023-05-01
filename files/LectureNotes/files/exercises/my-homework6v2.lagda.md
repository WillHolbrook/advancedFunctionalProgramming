# Week 6 - Homework Sheet

```agda
{-# OPTIONS --without-K --safe #-}

module exercises.my-homework6v2 where

private
 open import prelude hiding (Bool-elim)
 open import natural-numbers-functions hiding (_≤_ ; is-even ; +-assoc)
 open import List-functions
 open import decidability
 open import isomorphisms
```
We will also want to use some things from the Lab of Week 4:

```agda
 open import exercises.lab4-solutions
 open import exercises.lab5-solutions
```

## Part I: More on length

Besides `map`, the function `reverse` is another example of a length-preserving
operation.

```agda
 length-of-reverse : {A : Type} (xs : List A)
                   → length (reverse xs) ≡ length xs
 length-of-reverse [] = refl zero
 length-of-reverse (x :: xs) = 
   length (reverse xs ++ [ x ]) ≡⟨ length-of-++ (reverse xs) [ x ] ⟩
   length (reverse xs) + 1      ≡⟨ +-comm (length (reverse xs)) 1 ⟩
   suc (length (reverse xs))    ≡⟨ ap suc (length-of-reverse xs) ⟩
   suc (length xs)              ∎

```

**Prove** the above.

## Part II: More on isomorphisms

### Exercise 2a

```agda
 ℕ-[⋆]-iso : ℕ ≅ List 𝟙
 ℕ-[⋆]-iso = record { bijection = f ; bijectivity = f-is-bijection }
  where
   f : ℕ → List 𝟙
   f zero = []
   f (suc n) = ⋆ :: f n

   g : List 𝟙 → ℕ
   g [] = zero
   g (⋆ :: xs) = suc (g xs)

   gf : g ∘ f ∼ id
   gf zero = refl zero
   gf (suc n) = ap suc (gf n)

   fg : f ∘ g ∼ id
   fg [] = refl []
   fg (⋆ :: xs) = ap (⋆ ::_) (fg xs)

   f-is-bijection : is-bijection f
   f-is-bijection = record { inverse = g ; η = gf ; ε = fg }
```

**Show** that the type of natural numbers `ℕ` is isomorphic to the type of lists
over the unit type `𝟙`.

Hint: The statement of Exercise 2b may help you.

### Exercise 2b

```agda
 open _≅_

 ℕ→[⋆]-preserves-length : (n : ℕ) → length (bijection ℕ-[⋆]-iso n) ≡ n
 ℕ→[⋆]-preserves-length zero = refl zero
 ℕ→[⋆]-preserves-length (suc n) = ap suc (ℕ→[⋆]-preserves-length n)
```

Notice how `bijection` extracts the function `f` you defined in `ℕ-[⋆]-iso`.

**Prove** that for any `n : ℕ`, the length of the list `f n : List 𝟙`
(where `f : ℕ → List 𝟙` is as you defined in Exercise 3a) is `n`.

## Part III: More on evenness

In this exercise, we will continue where we left off in the lab exercises on
evenness. Recall the predicates `is-even` and `check-even`:

```agda
--  is-even : ℕ → Type
--  is-even x = Σ y ꞉ ℕ , x ≡ 2 * y
```

```agda
--  check-even : ℕ → Bool
--  check-even zero          = true
--  check-even (suc zero)    = false
--  check-even (suc (suc n)) = check-even n
```

Now recall the discussion about decidable predicates that we had in the previous
weeks. When you proved that `check-even` and `is-even` are logically equivalent
in the lab, you have in fact implicitly proved that `is-even` is a decidable
predicate! In this exercise, we will make this implicit proof _explicit_.

**Complete** the remaining holes in the following proof outline; starting with
proving a lemma stating that a Boolean is either `true` or `false`.

```agda
 true-is-not-false : ¬ (true ≡ false)
 true-is-not-false ()

 principle-of-bivalence : (b : Bool) → (b ≡ true) ∔ (b ≡ false)
 principle-of-bivalence true  = inl (refl true)
 principle-of-bivalence false = inr (refl false)

 is-even-is-decidable : (n : ℕ) → is-decidable (is-even n)
 is-even-is-decidable n =
  ∔-nondep-elim goal₁ goal₂ (principle-of-bivalence (check-even n))
   where
    goal₁ : check-even n ≡ true → is-decidable (is-even n)
    goal₁ p = inl (check-even⇒even n p)

    goal₂ : check-even n ≡ false → is-decidable (is-even n)
    goal₂ p = inr subgoal
     where
      subgoal : ¬ is-even n
      subgoal q = true-is-not-false (
        true ≡⟨ sym (even⇒check-even n q) ⟩
        check-even n ≡⟨ p ⟩
        false ∎
       )
```

## Part IV: Stretcher exercises on length

*The following two exercises are rather hard and are should be interesting to
students that like a challenge.*

Recall that we can define `filter` as
```agda
 filter : {A : Type} → (A → Bool) → List A → List A
 filter P []        = []
 filter P (x :: xs) = if P x then (x :: ys) else ys
  where
   ys = filter P xs
```

We also remind you of the inductively defined less-than-or-equal relation `≤`
on the natural numbers.

```agdacode
data _≤_ : ℕ → ℕ → Type where
  ≤-zero : (  y : ℕ) → 0 ≤ y
  ≤-suc  : (x y : ℕ) → x ≤ y → suc x ≤ suc y
```

Finally, the following lemmas are provided to you for your convenience.

```agda
 ≤-suc-lemma : (n : ℕ) → n ≤ (1 + n)
 ≤-suc-lemma 0       = ≤-zero (1 + 0)
 ≤-suc-lemma (suc n) = goal
  where
   IH : n ≤ (1 + n)
   IH = ≤-suc-lemma n
   goal : suc n ≤ suc (suc n)
   goal = ≤-suc n (suc n) IH

 Bool-elim : (A : Bool → Type)
           → A false
           → A true
           → (x : Bool) → A x
 Bool-elim A x₀ x₁ false = x₀
 Bool-elim A x₀ x₁ true  = x₁
```

### Exercise 4a (stretcher 🌶)

**Prove** that filtering a list decreases its length.

```agda
 length-of-filter : {A : Type} (P : A → Bool) (xs : List A)
                  → length (filter P xs) ≤ length xs
 length-of-filter p [] = ≤-zero zero
 length-of-filter p (x :: xs)
  = Bool-elim
    (λ b → (length (if b then x :: filter p xs else filter p xs)) ≤ (length (x :: xs)))
    (≤-trans (length (filter p xs)) (length xs) (suc (length xs)) (length-of-filter p xs) (≤-suc-lemma (length xs)))
    (≤-suc (length (filter p xs)) (length xs) (length-of-filter p xs))
    (p x)
```

*Hints*:
 - You can use `≤-trans` from the [sample solutions to
   Lab 4](lab4-solutions.lagda.md) if you need that `≤` is transitive.
   (The sample solutions are already imported for you.)
 - Think about how to use `Bool-elim`.

### Exercise 4b (stretcher 🌶🌶)

Given a predicate `P : A → Bool` and a list `xs : List A`, we could filter `xs`
by `P` and by `not ∘ P`. If we do this and compute the lengths of the resulting
lists, then we expect their sum to be equal to the length of the unfiltered list
`xs`. **Prove** this fact.

```agda
 length-of-filters : {A : Type} (P : A → Bool) (xs : List A)
                   → length (filter P xs) + length (filter (not ∘ P) xs)
                   ≡ length xs
 length-of-filters p [] = refl zero
 length-of-filters p (x :: xs)
  = Bool-elim
    (λ b →
      length (if b then x :: filter p xs else filter p xs) +
      length (if not b then x :: filter (λ y → not (p y)) xs else filter (λ y → not (p y)) xs)
      ≡ length (x :: xs)
    )
    (
     length (filter p xs) + suc (length (filter (λ y → not (p y)) xs)) ≡⟨ +-step _ _ ⟩
     suc (length (filter p xs) + length (filter (λ y → not (p y)) xs)) ≡⟨ ap suc (length-of-filters p xs) ⟩
     suc (length xs) ∎
    )
    (ap suc (length-of-filters p xs))
    (p x)
```

*Hint*: You can use associativity (`+-assoc`) and commutativity (`+-comm`) from
 the sample solutions to last week's exercises. (The necessary files are already
 imported for you.)

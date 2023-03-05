# Week 6 - Homework Sheet

```agda
{-# OPTIONS --without-K --safe #-}

module exercises.my-homework6 where

private
 open import prelude hiding (Bool-elim)
 open import natural-numbers-functions hiding (_≤_ ; is-even ; +-assoc ; +-comm)
 open import List-functions
 open import decidability
 open import isomorphisms
```
We will also want to use some things from the Lab of Week 4:

```agda
 open import exercises.lab4-solutions
```

## Part I: More on length

Besides `map`, the function `reverse` is another example of a length-preserving
operation.

```agda
 length-of-++ : {A : Type} (xs ys : List A)
              → length (xs ++ ys) ≡ length xs + length ys
 length-of-++ []        ys = refl (length ys)
 length-of-++ (x :: xs) ys = ap suc IH
   where
    IH : length (xs ++ ys) ≡ length xs + length ys
    IH = length-of-++ xs ys

 +-comm : (x y : ℕ) → x + y ≡ y + x
 +-comm 0       y = 0 + y       ≡⟨ refl _ ⟩
                    y           ≡⟨ sym (+-base y) ⟩
                    y + 0       ∎

 +-comm (suc x) y = suc x + y   ≡⟨ refl _ ⟩
                    suc (x + y) ≡⟨ ap suc (+-comm x y) ⟩
                    suc (y + x) ≡⟨ refl _ ⟩
                    suc y + x   ≡⟨ sym (+-step y x) ⟩
                    y + suc x   ∎

 length-of-reverse : {A : Type} (xs : List A)
                   → length (reverse xs) ≡ length xs
 length-of-reverse [] = refl zero
 length-of-reverse (x :: xs) =
   length (reverse xs ++ (x :: []))                 ≡⟨ length-of-++ (reverse xs) (x :: []) ⟩
   length (reverse xs) + length (reverse (x :: [])) ≡⟨ refl _ ⟩
   length (reverse xs) + 1                          ≡⟨ +-comm (length (reverse xs)) 1 ⟩
   1 + length (reverse xs)                          ≡⟨ refl _ ⟩
   suc (length (reverse xs))                        ≡⟨ ap suc (length-of-reverse xs) ⟩
   suc (length xs) ∎

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
   f (suc n) = ⋆ :: (f n)

   g : List 𝟙 → ℕ
   g [] = 0
   g (_ :: xs) = suc (g xs)

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
 is-even : ℕ → Type
 is-even x = Σ y ꞉ ℕ , x ≡ 2 * y
```

```agda
 check-even : ℕ → Bool
 check-even zero          = true
 check-even (suc zero)    = false
 check-even (suc (suc n)) = check-even n
```

Now recall the discussion about decidable predicates that we had in the previous
weeks. When you proved that `check-even` and `is-even` are logically equivalent
in the lab, you have in fact implicitly proved that `is-even` is a decidable
predicate! In this exercise, we will make this implicit proof _explicit_.

**Complete** the remaining holes in the following proof outline; starting with
proving a lemma stating that a Boolean is either `true` or `false`.

```agda
 +-suc-on-right : (x y : ℕ) → x + suc y ≡ suc (x + y)
 +-suc-on-right 0       y = refl (suc y)
 +-suc-on-right (suc x) y = ap suc (+-suc-on-right x y)

 evenness-lemma₂ : (n : ℕ) → is-even n → is-even (2 + n)
 evenness-lemma₂ n (k , p) = suc k , goal
  where
   goal : 2 + n ≡ 2 * suc k
   goal = 2 + n         ≡⟨ ap (suc ∘ suc) p ⟩
          2 + (k + k)   ≡⟨ ap suc (sym (+-suc-on-right k k)) ⟩
          suc k + suc k ∎

 check-even⇒even : (n : ℕ) → check-even n ≡ true → is-even n
 check-even⇒even zero prf = zero , refl zero
 check-even⇒even (suc (suc n)) prf = evenness-lemma₂ n (check-even⇒even n prf)

 not-1≡suc-suc : (n : ℕ) → ¬(1 ≡ suc (n + suc n))
 not-1≡suc-suc zero ()
 not-1≡suc-suc (suc n) ()

 evenness-lemma₁ : (n : ℕ) → is-even (2 + n) → is-even n
 evenness-lemma₁ n (suc k , p) = k , goal
  where
   subgoal : suc (suc n) ≡ suc (suc (2 * k))
   subgoal = suc (suc n)       ≡⟨ p ⟩
             suc k + suc k     ≡⟨ ap suc (+-suc-on-right k k) ⟩
             suc ((suc k) + k) ∎

   goal : n ≡ 2 * k
   goal = suc-is-injective (suc-is-injective subgoal)

 even⇒check-even : (n : ℕ) → is-even n → check-even n ≡ true
 even⇒check-even zero e = refl true
 even⇒check-even (suc zero) (suc zero , ())
 --(suc n/2 , prf) = 𝟘-elim (not-1≡suc-suc n/2 prf)
 even⇒check-even (suc (suc n)) e = even⇒check-even n (evenness-lemma₁ n e)

 principle-of-bivalence : (b : Bool) → (b ≡ true) ∔ (b ≡ false)
 principle-of-bivalence true = inl (refl true)
 principle-of-bivalence false = inr (refl false)

 false-is-not-true : ¬ (false ≡ true)
 false-is-not-true ()

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
      subgoal q = false-is-not-true (sym (trans (sym (even⇒check-even n q)) p))
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
 length-of-filter P [] = ≤-zero zero
 length-of-filter P (x :: xs) with P x
 length-of-filter P (x :: xs) | true = ≤-suc (length (filter P xs)) (length xs) (length-of-filter P xs)
 length-of-filter P (x :: xs) | false = ≤-trans (length (filter P xs)) (length xs) (suc (length xs)) (length-of-filter P xs) (≤-suc-lemma (length xs))

 length-of-filter' : {A : Type} (P : A → Bool) (xs : List A)
                   → length (filter P xs) ≤ length xs
 length-of-filter' P [] = ≤-zero zero
 length-of-filter' P (x :: xs) = Bool-elim goal-statement false-case true-case (P x)
   where
     filtered-tail = filter P xs
--     length (filter P (x :: xs)) ≤ length (x :: xs)
     goal-statement : Bool → Type
     goal-statement b = length (if b then (x :: filtered-tail) else filtered-tail) ≤ length (x :: xs)

     IH : length filtered-tail ≤ length xs
     IH = length-of-filter P xs

     false-case : length filtered-tail ≤ length (x :: xs)
     false-case = ≤-trans _ _ _ IH (≤-suc-lemma (length xs))

     true-case : length (x :: filtered-tail) ≤ length (x :: xs)
     true-case = ≤-suc _ _ IH
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
 length-of-filters P [] = refl zero
 length-of-filters P (x :: xs) with P x
 length-of-filters P (x :: xs) | true = ap suc (length-of-filters P xs)
 length-of-filters P (x :: xs) | false =
   length (filter P xs) + suc (length (filter (not ∘ P) xs)) ≡⟨ +-suc-on-right _ _ ⟩
   suc (length (filter P xs) + (length (filter (not ∘ P) xs))) ≡⟨ ap suc (length-of-filters P xs) ⟩
   suc (length xs) ∎

 length-of-filters' : {A : Type} (P : A → Bool) (xs : List A)
                    → length (filter P xs) + length (filter (not ∘ P) xs)
                    ≡ length xs
 length-of-filters' P [] = refl zero
 length-of-filters' P (x :: xs) = Bool-elim goal-statement false-case true-case (P x)
   where
     ys = filter P xs
     ys' = filter (not ∘ P) xs

     IH : length ys + length ys' ≡ length xs
     IH = length-of-filters' P xs
 
     goal-statement : Bool → Type
     goal-statement b = length (if b then (x :: ys) else ys) +
                        length (if (not b) then (x :: ys') else ys')
                      ≡ suc (length xs)

     true-case : length (x :: ys) + length ys' ≡ suc (length xs)
     true-case = ap suc IH

     false-case : length ys + length (x :: ys') ≡ suc (length xs)
     false-case =
       length ys + length (x :: ys') ≡⟨ refl _ ⟩
       length ys + suc (length ys') ≡⟨ +-suc-on-right _ _ ⟩
       suc (length ys + length ys') ≡⟨ ap suc IH ⟩
       suc (length xs) ∎
```

*Hint*: You can use associativity (`+-assoc`) and commutativity (`+-comm`) from
 the sample solutions to last week's exercises. (The necessary files are already
 imported for you.)


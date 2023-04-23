# Class Test 2

```agda
{-# OPTIONS --without-K --safe --auto-inline #-}

module exercises.old-test2 where

open import prelude
open import isomorphisms
open import List-functions
open import natural-numbers-functions
open import sorting
open import strict-total-order
```

## Important remarks

1. Put your student ID card on your desk.
1. You are not allowed to talk or use your phone during the test. If you do,
   this will be considered an instance of plagiarism.
1. You can use a web-browser only for reading the lecture notes and the Agda
   manual. If you use it for anything else, this will be considered an instance
   of plagiarism.
1. Please do not ask questions to the invigilators unless you think there is a
   mistake in the test.
1. You can do these questions in any order. In particular, if you cannot work
   out the proof of something, you can leave the hole empty and still use it in
   other questions and get full marks for those other questions.
1. Each of the five sections has equal weight (20% each).
1. Your answers will be marked on correctness *and* quality.
1. The test starts at 16:00. For students without extra time, your deadline is
   17:50. Students with extra time have a deadline of 18:20 or 18:50.
1. Submitting late incurs a 1% penalty per minute, but you *must* submit and
   leave the room by 10 minutes after your deadline.

## Question 1

The type `ℕ` of natural numbers contains _countably infinite_ inhabitants. But
the type `𝟙 ∔ ℕ` also contains the same number of inhabitants which means that
these types are actually isomorphic.

**Prove** this fact.

```agda
ℕ-is-isomorphic-to-𝟙∔ℕ : ℕ ≅ 𝟙 ∔ ℕ
ℕ-is-isomorphic-to-𝟙∔ℕ = record { bijection = f ; bijectivity = f-is-bijection }
 where
  f : ℕ → 𝟙 ∔ ℕ
  f zero = inl ⋆
  f (suc n) = inr n

  g : 𝟙 ∔ ℕ → ℕ
  g (inl ⋆) = zero
  g (inr n) = suc n

  gf : (g ∘ f) ∼ id
  gf zero = refl zero
  gf (suc n) = refl (suc n)

  fg : (f ∘ g) ∼ id
  fg (inl ⋆) = refl (inl ⋆)
  fg (inr n) = refl (inr n)

  f-is-bijection : is-bijection f
  f-is-bijection = record { inverse = g ; η = gf ; ε = fg }
```

## Question 2

In [List-functions.lagda.md](../List-functions.lagda.md) we defined the


```agda-code
length : {A : Type} → List A → ℕ
length []        = 0
length (x :: xs) = 1 + length xs
```

A downside of this definition is that it is not tail-recursive and therefore not
very efficient. One way to have a tail-recursive computation of the length of a
list is to introduce an accumulating parameter.

We define the functions

```agda
length-aux : {A : Type} → List A → ℕ → ℕ
length-aux []        k = k
length-aux (x :: xs) k = length-aux xs (suc k)

length-tail-rec : {A : Type} → List A → ℕ
length-tail-rec xs = length-aux xs 0
```

**Prove** the following lemma about `length-aux`

```agda
lemma : {A : Type} (xs : List A) (k : ℕ) → length-aux xs (suc k) ≡ suc (length-aux xs k)
lemma [] k = refl (suc k)
lemma (x :: xs) k = lemma xs (suc k)

length-aux-lemma : {A : Type} (xs : List A) (k : ℕ)
                 → length-aux xs k ≡ length xs + k
length-aux-lemma [] k = refl k
length-aux-lemma (x :: xs) k =
   length-aux xs (suc k) ≡⟨ lemma xs k ⟩
   suc (length-aux xs k) ≡⟨ ap suc (length-aux-lemma xs k) ⟩
   suc (length xs + k)   ∎

```

and use it to **conclude** that `length-tail-rec` is correct (in the sense that
it computes the same thing as `length`):

```agda
length-tail-rec-is-correct : {A : Type} (xs : List A) → length-tail-rec xs ≡ length xs
length-tail-rec-is-correct xs = 
   length-aux xs 0 ≡⟨ length-aux-lemma xs 0 ⟩
   length xs + 0   ≡⟨ +-base (length xs) ⟩
   length xs ∎

```

*Hint*: You can use `length-aux-lemma` in solving `length-is-correct`, even if
you don't manage to prove `length-aux-lemma`.

## Question 3

A function `f : X → Y` between two strict total orders `(X,<[X])` and `(Y,<[Y])`
is said to be *non-decreasing* if whenever `x <[X] x'` then either `f x' ≡ f x`
or `f x <[Y] f x'`.

We write this in Agda as follows

```agda
module _
        {X : Type}
        {Y : Type}
        (σ : StrictTotalOrder X)
        (τ : StrictTotalOrder Y)
       where

 open StrictTotalOrder

 _<[X]_ : X → X → Type
 _<[X]_ = _<_ σ
 _<[Y]_ : Y → Y → Type
 _<[Y]_ = _<_ τ

 is-non-decreasing : (X → Y) → Type
 is-non-decreasing f = (x x' : X) → x <[X] x'
                                  → (f x' ≡ f x) ∔ (f x <[Y] f x')
```

**Prove** that if `f` is a non-decreasing function, then `map f xs` is sorted
whenever the input list `xs` is sorted:

```agda
 map-of-non-decreasing-preserves-sorted : (f : X → Y) → is-non-decreasing f
                                        → (xs : List X) → Sorted σ xs
                                        → Sorted τ (map f xs)
 map-of-non-decreasing-preserves-sorted f m []              nil-sorted       = nil-sorted
 map-of-non-decreasing-preserves-sorted f m (x :: [])       sing-sorted      = sing-sorted
 map-of-non-decreasing-preserves-sorted f m (x :: .x :: xs) (adj-sorted s (inl (refl .x)))
   = adj-sorted (map-of-non-decreasing-preserves-sorted f m (x :: xs) s) (inl (refl (f x)))
 map-of-non-decreasing-preserves-sorted f m (x :: x' :: xs) (adj-sorted s (inr x<x'))
   = adj-sorted (map-of-non-decreasing-preserves-sorted f m (x' :: xs) s) (m x x' x<x')
```

## Question 4

We define a type of binary trees with nodes storing values:

```agda
data BinTree (X : Type) : Type where
 Leaf : BinTree X
 Node : BinTree X → X → BinTree X → BinTree X
```

For example,

```agda
example-BinTree : BinTree ℕ
example-BinTree = Node (Node Leaf 9 (Node Leaf 4 Leaf)) 17 (Node Leaf 3 Leaf)
```

represents the binary tree
```picture
          17
          / \
         /   \
        /     \
       9       3
      / \     / \
         4
        / \
```

We can define *binary search trees* as follows:

1. A leaf is a binary search tree.
1. If `l` and `r` are binary search trees, and every node of `l` is strictly
smaller than `x`, and every node of `r` is strictly bigger than `x`, then
`Node x l r` is a binary search tree.

The tree above is *not* a binary search tree, because (for example) 3 is not 
greater than or equal to 17.

But the tree
```picture
           9
          / \
         /   \
        /     \
       3      17
      / \     / \
         4
        / \
```
is an example of a binary search tree.


### Question 4.1

Given a type `X` with a strict total order, we ask you to **define** two predicates
`all-smaller : BinTree X → X → Type` and `all-bigger : BinTree X → X → Type`
such that

1. We have that `all-smaller t x` if all the nodes in the binary tree `t` are
stricly smaller than `x`.
1. We have that `all-bigger t x` if all the nodes in the binary tree `t` are
strictly bigger than `x`.

```agda
all-smaller : {X : Type} → StrictTotalOrder X → BinTree X → X → Type
all-smaller τ Leaf x = 𝟙
all-smaller {X} τ (Node bin₁ y bin₂) x = (all-smaller τ bin₁ x) × (y <x x) × all-smaller τ bin₂ x
  where
   open StrictTotalOrder

   _<x_ : X → X → Type
   _<x_ = _<_ τ

all-bigger : {X : Type} → StrictTotalOrder X → BinTree X → X → Type
all-bigger τ Leaf x = 𝟙
all-bigger {X} τ (Node bin₁ y bin₂) x = all-bigger τ bin₁ x × (x <x y) × all-bigger τ bin₂ x
  where
   open StrictTotalOrder

   _<x_ : X → X → Type
   _<x_ = _<_ τ
```


### Question 4.2

Given a type `X` with a strict total order, we ask you to **define** a predicate
`is-bst : BinTree X → Type` such that `is-bst t` expresses that the binary tree
`t` is a binary search tree.

```agda
is-bst : {X : Type} → StrictTotalOrder X → BinTree X → Type
is-bst τ Leaf = 𝟙
is-bst {X} τ (Node bin₁ x bin₂) = all-smaller τ bin₁ x × all-bigger τ bin₂ x × is-bst τ bin₁ × is-bst τ bin₂
  where
   open StrictTotalOrder

   _<x_ : X → X → Type
   _<x_ = _<_ τ
```

*Hint:* You will find it helpful to use the predicates from Question 4.1, even if you did not finish defining them.

### Write your solutions for 4.1 and 4.2 here

For both parts, you can use `data` or instead a recursive definition, as you prefer.

```agda
module _
        {X : Type}
        (σ : StrictTotalOrder X)
       where

 open StrictTotalOrder σ

```

## Question 5 (Hard! 🌶)

The [famous diagonalisation argument of
Cantor](https://en.wikipedia.org/wiki/Cantor%27s_diagonal_argument)
was used to show that `ℕ → Bool` _does not_ have the same number of
inhabitants as `ℕ`. This means an isomorphism `ℕ ≃ ℕ → Bool` cannot
exist. Your task is to prove this in the following steps.

### Question 5.1

A sequence of booleans is just a function `t : ℕ → Bool`. The terms of
the sequence `t` are `t 0`, `t 1`, `t 2` , ⋯.

Now suppose you have a sequence of sequences of booleans. This is just a function `s : ℕ → (ℕ → Bool)`. The first sequence is `s 0`, the second one is `s 1` and so on. Here is an example:

![famous diagonalisation argument of
Cantor](diag.svg)

Your task is, given `s : ℕ → (ℕ → Bool)`, produce a sequence `diag s : ℕ → Bool` such that `diag s` is different from `s n` for every `n : ℕ`. Use the picture to figure out how to define `diag`:

```agda
diag : (ℕ → (ℕ → Bool)) → (ℕ → Bool)
diag s n = not (s n n)
```

Now prove that this works:
```agda
not-lemma : (b : Bool) → ¬ (not b ≡ b)
not-lemma true ()
not-lemma false ()

diag-correct : (s : ℕ → (ℕ → Bool))
             → (n : ℕ) → ¬ (diag s ∼ s n)
diag-correct s n x = not-lemma (s n n) (x n)
```

### Question 5.2

Use the functions from Question 5.1, even if you did not finish them, to complete the 
proof that there can be no isomorphism between `ℕ` and `ℕ → Bool`.

```agda
ℕ≃ℕ→Bool-is-impossible : ¬ (ℕ ≅ (ℕ → Bool))
ℕ≃ℕ→Bool-is-impossible (Isomorphism f (Inverse g η ε)) = diag-correct f (g (diag f)) (λ x → sym (ap (λ m → m x) (ε (diag f))))
```

# Test 1

```agda
{-# OPTIONS --without-K --safe --auto-inline #-}

module exercises.test1 where

open import prelude
open import natural-numbers-functions
open import List-functions
open import isomorphisms
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
1. The test starts at 16:00. For students with extra time, your test starts at 15:30.
All students finish at 17:50, with 5% penalty for submissions at 18:00. No submissions are possible after 18:00, so make sure you submit before 18:00.
1. You must not leave the room between 17:40 and 17:50 to avoid disruption.

## Please check your Canvas submission after you have submitted

This is necessary to make sure you submitted the file you intended to submit. Often students accidentally submit the wrong file.

It is also a good idea to submit to Canvas well before the deadline when you have completed enough questions. We will mark the latest submission.

## Question 1

This question concerns the following functions, first defined in `Bool.lagda.md`.

```agdacode
if_then_else_ : {A : Type} → Bool → A → A → A
if true  then x else y = x
if false then x else y = y

_&&_ : Bool → Bool → Bool
true  && y = y
false && y = false

_||_ : Bool → Bool → Bool
true  || y = true
false || y = y
```

We didn't have to define `_&&_` and `_||_` using pattern matching.
We could have instead used `if_then_else_`.

First, **redefine** the functions `_&&_` and `_||_` using `if_then_else_` by filling the below holes.

```agda
_&&'_ : Bool → Bool → Bool
a &&' b = if a then b else false

_||'_ : Bool → Bool → Bool
a ||' b = if a then true else b
```

Now, **prove** that, in each case, the functions act identically.

```agda
and-defined-with-if : (a b : Bool) → a && b ≡ a &&' b
and-defined-with-if = {!!} 

or-defined-with-if  : (a b : Bool) → a || b ≡ a ||' b
or-defined-with-if = {!!} 
```

## Question 2

In this exercise, we will define an inductively defined type expressing the
_sublist relationship_ between two lists.

Consider two lists `xs ys : List ℕ`. The type `xs is-a-sublist-of ys` should
express that `xs` can be obtained by deleting (at any position) some or no
elements of `ys`.

Your type definition should have three constructors corresponding
to the following inductive rules:

0. The empty list is a sublist of any list;
1. A sublist remains a sublist of a list extended with one element at the head;
2. Given a sublist `xs` of a list `ys`, extending `xs` and `ys` with the same
   element at the head preserves the sublist relation.

Here are some examples of this relation:

- `[1]` is a sublist of `[1, 2]` because deleting `2` from the latter gives
  the former.
- `[2]` is a sublist of `[1, 2]` because deleting `1` from the latter gives
  the former.
- `[2, 4, 6]` is a sublist of `[1, 2, 3, 4, 5, 6]` because deleting `1`,
  `3`, and `5` from the latter gives the former.

**Define** the types of constructors `subl₀`, `subl₁`, and `subl₂` so that
they correspond to the above inductive rules.

```agda
data _is-a-sublist-of_ : List ℕ → List ℕ → Type where
 subl₀ : (ns : List ℕ)
         → {!!} is-a-sublist-of {!!}
 subl₁ : {xs ys : List ℕ} (y : ℕ)
         → {!!}
         → {!!} is-a-sublist-of {!!}
 subl₂ : {xs ys : List ℕ} (y : ℕ)
         → {!!}
         → {!!} is-a-sublist-of {!!}
```

Complete the following proofs using this relation:

```agda
sublist-example₁ : [ 1 ] is-a-sublist-of (1 :: 2 :: [])
sublist-example₁ = {!!}

sublist-example₂ : (2 :: []) is-a-sublist-of (1 :: 2 :: [])
sublist-example₂ = {!!}

sublist-example₃ : (2 :: 4 :: 6 :: [])
                        is-a-sublist-of
                       (1 :: 2 :: 3 :: 4 :: 5 :: 6 :: [])
sublist-example₃ = {!!}
```

## Question 3

The cartesian product `×` satisfies the same equations as multiplication of
natural numbers.

For example, remembering that `Bool` has 2 elements, `X × Bool ≅ X ∔ X`.

The type `X × Bool` tags an element `x : X` with either `true` or `false`,
whereas the type `X + X` tags an element `x : X` with either `inl` or `inr`.
In both cases, there are two tags, and thus the types are isomorphic.

**Prove** this isomorphism.

```agda
bool-+-iso : (X : Type) → X × Bool ≅ X ∔ X
bool-+-iso X =
 record { bijection  = f
        ; bijectivity = record { inverse = g ; η = section ; ε = retraction } }
  where
   f : X × Bool → X ∔ X
   f = {!!} 

   g : X ∔ X → X × Bool
   g = {!!} 

   section : g ∘ f ∼ id
   section = {!!}

   retraction : f ∘ g ∼ id
   retraction = {!!} 
```

## Question 4 

We can define the list membership relation `∈` as follows:

```agda
data _∈_ {X : Type} : X → List X → Type where
  head-case : (x : X) (xs : List X) → x ∈ (x :: xs)
  tail-case : (x : X) (xs : List X) → x ∈ xs → (y : X) → x ∈ (y :: xs)
```

Given a boolean valued predicate `P : X → Bool`, recall that the
`filter` function scans the list, retaining only those elements `x`
for which `P x` evaluates to `true`.  Here is its definition:

```agda
filter : {X : Type} (P : X → Bool) → List X → List X
filter P [] = []
filter P (x :: xs) = if (P x) then (x :: filter P xs) else (filter P xs)
```

**Formulate** the following statement about the `filter` function:

if filtering a list `xs` by a predicate `P` results in a list which is
equal to the original, then the predicate `P` evaluates to `true` on
every member of the list.


```agda
filter-property : (X : Type) (P : X → Bool) (xs : List X) → Type
filter-property X P xs = {!!}
```

*Note*: You must not change the type of `filter-property`.  Moreover,
 we do not ask you to prove the resulting statement.

## Question 5 (Hard 🌶🌶🌶) 

Given a function `f : X → X`, we say that an element `x : X` is a 
*fixed point of `f`* if `f x = x`. 

**Define** a predicate expressing the fact that a given element `x : X`
is a fixed point of a function `f`.

```agda
is-fixed-point-of : {!!}
is-fixed-point-of = {!!} 
```
Now, **state** *and* **prove** the following: if every member `x` of
a list `l : List X` is a fixed point of `f`, then `l` is a fixed point
of the function `map f`.

```agda
list-fixed-point : {!!}
list-fixed-point = {!!} 
```

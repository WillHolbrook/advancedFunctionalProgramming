# Test 1

```agda
{-# OPTIONS --without-K --safe --auto-inline #-}

module exercises.my-test1 where

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
and-defined-with-if true b = refl b
and-defined-with-if false b = refl false

or-defined-with-if  : (a b : Bool) → a || b ≡ a ||' b
or-defined-with-if true b = refl true
or-defined-with-if false b = refl b
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
         → [] is-a-sublist-of ns
 subl₁ : {xs ys : List ℕ} (y : ℕ)
         → xs is-a-sublist-of ys
         → xs is-a-sublist-of (y :: ys)
 subl₂ : {xs ys : List ℕ} (y : ℕ)
         → xs is-a-sublist-of ys
         → (y :: xs) is-a-sublist-of (y :: ys)
```

Complete the following proofs using this relation:

```agda
sublist-example₁ : [ 1 ] is-a-sublist-of (1 :: 2 :: [])
sublist-example₁ = subl₂ 1 (subl₀ (2 :: []))

sublist-example₂ : (2 :: []) is-a-sublist-of (1 :: 2 :: [])
sublist-example₂ = subl₁ 1 (subl₂ 2 (subl₀ []))

sublist-example₃ : (2 :: 4 :: 6 :: [])
                        is-a-sublist-of
                       (1 :: 2 :: 3 :: 4 :: 5 :: 6 :: [])
sublist-example₃ = subl₁ 1
                     (subl₂ 2 (subl₁ 3 (subl₂ 4 (subl₁ 5 (subl₂ 6 (subl₀ []))))))

sublist-example₄ : ¬ ([ 2 ] is-a-sublist-of [ 3 ])
sublist-example₄ (subl₁ .3 ())
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
   f (x , true) = inl x
   f (x , false) = inr x

   g : X ∔ X → X × Bool
   g (inl x) = x , true
   g (inr x) = x , false

   section : g ∘ f ∼ id
   section (x , true) = refl (x , true)
   section (x , false) = refl (x , false)

   retraction : f ∘ g ∼ id
   retraction (inl x) = refl (inl x)
   retraction (inr x) = refl (inr x)
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
filter-property X P xs = filter P xs ≡ xs → (x : X) → x ∈ xs → P x ≡ true

data _<_ : ℕ → ℕ → Type where
  <-zero : {  y : ℕ} → 0 < suc y
  <-suc : {x y : ℕ} → x < y → suc x < suc y

pop-list : {X : Type} → List X → List X
pop-list [] = []
pop-list (x :: xs) = xs

lemma : {X : Type}{x : X}{xs ys : List X} → _≡_ {List X} (x :: xs) (x :: ys) → xs ≡ ys
lemma eq = ap pop-list eq

suc-≤-imp-< : {x y : ℕ} → x ≤ y → x < suc y
suc-≤-imp-< {0} {y} x≤y = <-zero
suc-≤-imp-< {suc x} {suc y} x≤y = <-suc (suc-≤-imp-< (suc-reflects-≤ x≤y))

<-imp-¬eq : {x y : ℕ} → x < y → ¬ (x ≡ y)
<-imp-¬eq {1} {.1} (<-suc ()) (refl .1)
<-imp-¬eq {.(suc (suc _))} {.(suc (suc _))} (<-suc (<-suc x<y)) (refl .(suc (suc _))) = <-imp-¬eq x<y (refl _)

≤-suc-lemma : (n : ℕ) → n ≤ (1 + n)
≤-suc-lemma 0       = 0-smallest 
≤-suc-lemma (suc n) = goal
 where
  IH : n ≤ (1 + n)
  IH = ≤-suc-lemma n
  goal : suc n ≤ suc (suc n)
  goal = suc-preserves-≤ IH

≤-trans : (x y z : ℕ) → x ≤ y → y ≤ z → x ≤ z
≤-trans zero y z p q  = 0-smallest
≤-trans (suc x) (suc y) (suc z) (suc-preserves-≤ p) (suc-preserves-≤ q)
 = suc-preserves-≤ (≤-trans x y z p q)

length-of-filter : {A : Type} (P : A → Bool) (xs : List A)
                 → length (filter P xs) ≤ length xs
length-of-filter P []        = 0-smallest
length-of-filter P (x :: xs) = Bool-elim goal-statement true-case false-case (P x)
 where
  ys = filter P xs
  
  goal-statement : Bool → Type
  goal-statement b = length (if b then (x :: ys) else ys) ≤ length (x :: xs)

  IH : length ys ≤ length xs
  IH = length-of-filter P xs

  false-case : length ys ≤ length (x :: xs)
  false-case = ≤-trans (length ys) (length xs) (length (x :: xs))
                 IH (≤-suc-lemma (length xs))

  true-case : length (x :: ys) ≤ length (x :: xs)
  true-case = suc-preserves-≤ IH

suc-on-right-≤ : {x y : ℕ} → x ≤ y → x ≤ suc y
suc-on-right-≤ {zero} {zero} x≤y = 0-smallest
suc-on-right-≤ {zero} {suc y} x≤y = 0-smallest
suc-on-right-≤ {suc x} {suc y} (suc-preserves-≤ x≤y) = suc-preserves-≤ (suc-on-right-≤ x≤y)

lemma2 : {X : Type}(x : X)(xs : List X)(P : X → Bool) → filter P (x :: xs) ≡ x :: xs → filter P xs ≡ xs
lemma2 x [] P eq = refl []
lemma2 x (y :: xs) P eq with P x
lemma2 x (y :: xs) P eq | true = ap pop-list eq
lemma2 x (y :: xs) P eq | false with P y
lemma2 x (y :: xs) P eq | false | true
  = 𝟘-elim (<-imp-¬eq (suc-≤-imp-< (length-of-filter P xs)) (ap (pred ∘ length) eq))
lemma2 x (y :: xs) P eq | false | false = 𝟘-elim (<-imp-¬eq (suc-≤-imp-< (suc-on-right-≤ (length-of-filter P xs))) (ap length eq))

check-filter-property : {X : Type}(P : X → Bool)(xs : List X) → filter-property X P xs
check-filter-property P (x :: []) eq .x (head-case .x .[]) with P x
check-filter-property P (x :: []) eq .x (head-case .x .[]) | true = refl true
check-filter-property P (y :: z :: xs) eq .y (head-case .y .(z :: xs)) with P y
check-filter-property P (y :: z :: xs) eq .y (head-case .y .(z :: xs)) | true = refl true
check-filter-property P (y :: z :: xs) eq .y (head-case .y .(z :: xs)) | false with P z
check-filter-property {X} P (y :: z :: xs) eq .y (head-case .y .(z :: xs)) | false | true
  = 𝟘-elim (<-imp-¬eq (suc-≤-imp-< (length-of-filter P xs)) (ap (pred ∘ length) eq))
check-filter-property P (y :: z :: xs) eq .y (head-case .y .(z :: xs)) | false | false
  = 𝟘-elim (<-imp-¬eq (suc-≤-imp-< (suc-on-right-≤ (length-of-filter P xs))) (ap length eq))
check-filter-property P (y :: z :: xs) eq x (tail-case .x .(z :: xs) xinxs .y) with P y
check-filter-property P (y :: z :: xs) eq x (tail-case .x .(z :: xs) xinxs .y) | true
  = check-filter-property P (z :: xs) (ap pop-list eq) x xinxs
check-filter-property P (y :: z :: xs) eq x (tail-case .x .(z :: xs) xinxs .y) | false with P x
check-filter-property P (y :: z :: xs) eq x (tail-case .x .(z :: xs) xinxs .y) | false | true = refl true
check-filter-property P (y :: z :: xs) eq x (tail-case .x .(z :: xs) xinxs .y) | false | false with P z
check-filter-property P (y :: z :: xs) eq x (tail-case .x .(z :: xs) xinxs .y) | false | false | true
  = 𝟘-elim (<-imp-¬eq (suc-≤-imp-< (length-of-filter P xs)) (ap (pred ∘ length) eq))
check-filter-property P (y :: z :: xs) eq x (tail-case .x .(z :: xs) xinxs .y) | false | false | false
  = 𝟘-elim (<-imp-¬eq (suc-≤-imp-< (suc-on-right-≤ (length-of-filter P xs))) (ap length eq))

check-filter-property-int : (P : ℕ → Bool)(xs : List ℕ) → filter-property ℕ P xs
check-filter-property-int P xs = check-filter-property P xs
--TODO prove filter property for ints
--check-filter-property P (z :: xs) {!!} x xinxs
```

*Note*: You must not change the type of `filter-property`.  Moreover,
 we do not ask you to prove the resulting statement.

## Question 5 (Hard 🌶🌶🌶) 

Given a function `f : X → X`, we say that an element `x : X` is a 
*fixed point of `f`* if `f x = x`. 

**Define** a predicate expressing the fact that a given element `x : X`
is a fixed point of a function `f`.

```agda
_is-fixed-point-of_ : {X : Type}(x : X)(f : X → X) → Type
_is-fixed-point-of_ {X} x f = f x ≡ x 
```
Now, **state** *and* **prove** the following: if every member `x` of
a list `l : List X` is a fixed point of `f`, then `l` is a fixed point
of the function `map f`.

```agda
list-fixed-point : {X : Type}(l : List X)(f : X → X)
  → ((x : X) → x ∈ l → x is-fixed-point-of f) -- for all x where x is an element of the list x is a fixedpoint of f
  → l is-fixed-point-of (map f)
list-fixed-point [] f elem→fixp = refl []
list-fixed-point (x :: l) f elem→fixp =
  f x :: map f l ≡⟨ ap (_:: map f l) (elem→fixp x (head-case x l)) ⟩
  x :: map f l ≡⟨ ap (x ::_) (list-fixed-point l f λ y z → elem→fixp y (tail-case y l z x)) ⟩
  x :: l ∎

--Logically reads as
--For all list of type X and all functions of type X → X
--If for all x where x is an element of the list x is a fixedpoint of f
--Then l is a fixed point of f

--λ x z → elem→fixp x (tail-case x l z x₁)
-- list-fixed-point : {X : Type}(l : List X)(x : X)(f : X → X)
--   → x ∈ l
--   → is-fixed-point-of f x
--   → is-fixed-point-of (map f) l
-- list-fixed-point (x :: []) .x f (head-case .x .[]) xfixpf = ap (_:: []) xfixpf
-- -- ap {!!} {!!}
-- --f x :: [] ≡ x :: []
-- list-fixed-point (x :: z :: l) .x f (head-case .x .(z :: l)) xfixpf = {!!}
--   where
--     IH : {!!}
--     IH = list-fixed-point (z :: l) z f (head-case z l) {!!}
-- list-fixed-point (y :: z :: l) x f (tail-case .x .(z :: l) xinl .y) xfixpf =
--   f y :: f z :: map f l ≡⟨ ap (_:: f z :: map f l) {!!} ⟩
--   y :: f z :: map f l ≡⟨ {!!} ⟩
--   {!!} ≡⟨ {!!} ⟩
--   {!!} ≡⟨ {!!} ⟩
--   {!!} ≡⟨ {!!} ⟩
--   {!!} ≡⟨ {!!} ⟩
--   y :: z :: l ∎
--   where
--     IH : f z :: map f l ≡ z :: l
--     IH = list-fixed-point (z :: l) x f xinl xfixpf
```

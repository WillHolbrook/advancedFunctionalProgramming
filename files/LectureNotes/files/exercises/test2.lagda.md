# Test 2

```agda
{-# OPTIONS --without-K --safe --auto-inline #-}

module exercises.test2 where

open import prelude
open import natural-numbers-functions
open import List-functions
open import isomorphisms
open import decidability
open import strict-total-order

```

## Important remarks

1. Put your student ID card on your desk.
1. You are not allowed to talk or use your phone during the test. If you do,
this will be considered an instance of plagiarism.
1. You can use a web-browser only for reading the lecture notes and the Agda
manual. If you use it for anything else, this will be considered an instance of
plagiarism.
1. Please do not ask questions to the invigilators unless you think there is a
mistake in the test.
1. You can do these questions in any order. In particular, if you cannot work
out the proof of something, you can leave the hole empty and still use it in
other questions and get full marks for those other questions.
1. Each of the five sections has equal weight (20% each).
1. Your answers will be marked on correctness *and* quality.
1. The test starts at 16:00. For students with extra time, your test starts at
15:30. All students finish at 17:50, with 5% penalty for submissions at 18:00.
No submissions are possible after 18:00, to make sure you submit before 18:00.
1. You must not leave the room between 17:40 and 17:50 to avoid disruption.

## Please check your Canvas submission after you have submitted

This is necessary to make sure you submitted the file you intended to submit.
Often students accidentally submit the wrong file.

It is also a good idea to submit to Canvas well before the deadline when you
have completed enough questions. We will mark the latest submission.

## Question 1 - Evens and Odds are Isomorphic

Recall the definitions of `is-even` and `is-odd` from the
[natural numbers functions](../natural-numbers-functions.lagda.md) module.
We can define the types of even and odd natural numbers using a `Σ`-type as
follows:

```agda
evens : Type
evens = Σ n ꞉ ℕ , is-even n

odds : Type
odds = Σ n ꞉ ℕ , is-odd n
```
Show that these types are isomorphic:

```agda
ap-pred-ap-suc-lemma : (n m : ℕ) (e : n ≡ m) → ap pred (ap suc e) ≡ e
ap-pred-ap-suc-lemma n .n (refl .n) = refl (refl n)

ap-suc-ap-pred-lemma : (n m : ℕ) (e : suc n ≡ suc m) → ap suc (ap pred e) ≡ e
ap-suc-ap-pred-lemma n .n (refl .(suc n)) = refl (refl (suc n))

evens-isomorphic-to-odds : evens ≅ odds
evens-isomorphic-to-odds = record { bijection = f ; bijectivity = f-is-bijection }
 where
  f : evens → odds
  f (zero , k , n=k+k) = (suc zero) , (k , (ap suc n=k+k))
  f (suc zero , suc zero , ())
  f (suc zero , suc (suc k) , ())
  f (suc (suc n) , k , n=k+k) = (suc (suc (suc n))) , (k , (ap suc n=k+k))

  g : odds → evens
  g (suc zero , k , n=sk+k) = zero , (k , (ap pred n=sk+k))
  g (suc (suc zero) , suc zero , ())
  g (suc (suc zero) , suc (suc k) , ())
  g (suc (suc (suc n)) , k , n=sk+k) = suc (suc n) , k , (ap pred n=sk+k)

  gf : g ∘ f ∼ id
  gf (zero , k , n=k+k) = ap (λ e → 0 , k , e) (ap-pred-ap-suc-lemma zero (k + k) n=k+k)
  gf (suc zero , suc zero , ())
  gf (suc zero , suc (suc k) , ())
  gf (suc (suc n) , k , n=k+k) = ap (λ e → suc (suc n) , k , e) (ap-pred-ap-suc-lemma (suc (suc n)) (k + k) n=k+k)

  fg : f ∘ g ∼ id
  fg (suc zero , k , n=sk+k) = ap (λ e → 1 , k , e) (ap-suc-ap-pred-lemma zero (k + k) n=sk+k)
  fg (suc (suc zero) , suc zero , ())
  fg (suc (suc zero) , suc (suc k) , ())
  fg (suc (suc (suc n)) , k , n=sk+k) = ap (λ e → suc (suc (suc n)) , k , e) (ap-suc-ap-pred-lemma (suc (suc n)) (k + k) n=sk+k)

  f-is-bijection : is-bijection f
  f-is-bijection = record { inverse = g ; η = gf ; ε = fg }

```

## Question 2 - Zero is the only additive unit

Show that if the "addition by `n`" map `(λ k → n + k)` is a bijection for a
given `n : ℕ` (i.e. that `n` is an *additive unit*), then `n ≡ 0`:

```agda
lemma : (x y : ℕ) → ¬ (suc (x + y) ≡ x)
lemma zero y = λ ()
lemma (suc x) y = λ e → lemma x y (ap pred e)

zero-only-unit : (n : ℕ) → is-bijection (λ k → n + k) → n ≡ 0
zero-only-unit zero (Inverse g gf fg) = refl zero
zero-only-unit (suc b) (Inverse g gf fg) = 𝟘-elim {λ _ → suc b ≡ 0} (lemma b (g b) (fg b))
```

## Question 3 - Linear search

This question will make use of the membership predicate on lists:
```agda
data _∈_ {X : Type} : X → List X → Type where
  head-case : (x : X) (xs : List X) → x ∈ (x :: xs)
  tail-case : (x : X) (xs : List X) → x ∈ xs → (y : X) → x ∈ (y :: xs)
```
as well as the `Maybe` type constructor:
```agda
data Maybe (X : Type) : Type where
  Just : X → Maybe X
  Nothing : Maybe X
```
Throughout, we will suppose that we are working with a type `X` which has
decidable equality:
```agda
module _ {X : Type} (η : has-decidable-equality X) where
```
Consider the following specification of a linear search algorithm:
```
  record IncompleteSearchSpec : Type where
    field
      search : List X → X → Maybe X
      search-finds : (xs : List X) (y : X) → y ∈ xs → search xs y ≡ Just y

  open IncompleteSearchSpec
```
Notice that these two fields do not correctly specify our searching algorithm,
since it does not exclude the following trivial implementation where we simply
return the element being searched for, without inspecting the list:
```agda
  problematic-search : IncompleteSearchSpec
  problematic-search = record { search = trivial-search ; search-finds = trivial-search-finds }

    where trivial-search : List X → X → Maybe X
          trivial-search xs y = Just y

          trivial-search-finds : (xs : List X) (y : X) → y ∈ xs → trivial-search xs y ≡ Just y
          trivial-search-finds xs y y∈xs = refl (Just y)
```
Fill in the remaining hole in order to correctly describe the searching algorithm:
```agda
  record SearchingAlgorithm : Type where
    field
      search : List X → X → Maybe X
      search-finds : (xs : List X) (y : X) → y ∈ xs  → search xs y ≡ Just y
      search-complete : (xs : List X) (y : X) → ¬ (y ∈ xs) → search xs y ≡ Nothing

-- TODO Think more about this to see if correct
```
Now implement a linear search algorithm:

```
  search-implementation : SearchingAlgorithm
  search-implementation = record { search = linear-search
                                 ; search-finds = linear-search-finds
                                 ; search-complete = linear-search-complete }

    where  linear-search : List X → X → Maybe X
           linear-search [] x = Nothing
           linear-search (y :: xs) x with η y x
           linear-search (y :: xs) y | inl (refl y) = Just y
           linear-search (y :: xs) x | inr ¬x=y = linear-search xs x

           linear-search-finds : (xs : List X) (y : X) → y ∈ xs → linear-search xs y ≡ Just y
           linear-search-finds (x :: xs) y yinxs with η x y
           linear-search-finds (x :: xs) .x yinxs | inl (refl .x) = refl (Just x)
           linear-search-finds (x :: xs) .x (head-case .x .xs) | inr ¬x=y = 𝟘-elim {λ _ → linear-search xs x ≡ Just x} (¬x=y (refl x))
           linear-search-finds (x :: xs) y (tail-case .y .xs yinxs .x) | inr ¬x=y = linear-search-finds xs y yinxs

           linear-search-complete : (xs : List X) (y : X) → ¬ (y ∈ xs) → linear-search xs y ≡ Nothing
           linear-search-complete [] y ¬yinxs = refl Nothing
           linear-search-complete (x :: xs) y ¬yinxs with η x y
           linear-search-complete (x :: xs) .x ¬yinxs | inl (refl .x) = 𝟘-elim (¬yinxs (head-case x xs))
           linear-search-complete (x :: xs) y ¬yinxxs | inr ¬x=y = linear-search-complete xs y (λ yinxs → ¬yinxxs (tail-case y xs yinxs x))
```


## Question 4 - Lexicographic order on List ℕ

The *lexicographic* order on `List ℕ` is characterized by recusively comparing
head elements (using the underlying order on `ℕ`) and defining shorter lists to
precede longer ones otherwise.

The following lists are displayed in lexicographic order with smallest at the
top and largest at the bottom:

```text
[]
[0,7]
[0,7,8]
[2,4,7,6]
[2,5,3]
[4,6]
[7]
```

Implement this order.

**Note**.  The strict order on `ℕ` itself is implemented in the
  [strict-total-order](../strict-total-order.lagda.md) file, which is already in
  scope.  You may use a recursive definition as provided in the template below,
  or convert the template to an inductive definition (using `data`) if you
  prefer.

The agda mode shortcut for 'ₗ' is '\_l'.

```agda
_<ₗ_ : List ℕ → List ℕ → Type
xs <ₗ [] = 𝟘
[] <ₗ (y :: ys) = 𝟙
(x :: xs) <ₗ (y :: ys) = (x <ₙ y) ∔ ((x ≡ y) × (xs <ₗ ys))

_ : [] <ₗ (0 :: 7 :: [])
_ = ⋆

_ : (0 :: 7 :: []) <ₗ (0 :: 7 :: 8 :: [])
_ = inr ((refl zero) , (inr ((refl 7) , ⋆)))

_ : (2 :: 5 :: 3 :: []) <ₗ (4 :: 6 :: [])
_ = inl (<-suc (<-suc <-zero))

my-example : ¬ ([ 7 ] <ₗ [])
my-example ()
```
Now prove that this order is *irreflexive* and *transitive*.
```agda
<ₗ-irreflexive : (ns : List ℕ) → ¬ (ns <ₗ ns)
<ₗ-irreflexive [] = λ z → z
<ₗ-irreflexive (x :: ns) = IH
 where
  IH : ¬ ((x <ₙ x) ∔ ((x ≡ x) × (ns <ₗ ns)))
  IH (inl x<x) = <ₙ-irreflexive x x<x
  IH (inr (x=x , ns<ns)) = <ₗ-irreflexive ns ns<ns

<ₗ-transitive : {x y z : List ℕ} → x <ₗ y → y <ₗ z → x <ₗ z
<ₗ-transitive {[]} {y :: ys} {z :: zs} xs<ys ys<zs = ⋆
<ₗ-transitive {x :: xs} {y :: ys} {z :: zs} (inl x<y) (inl y<z) = inl (<ₙ-trans x<y y<z)
<ₗ-transitive {x :: xs} {y :: ys} {.y :: zs} (inl x<y) (inr (refl .y , ys<zs)) = inl x<y
<ₗ-transitive {x :: xs} {.x :: ys} {z :: zs} (inr (refl .x , xs<ys)) (inl x<z) = inl x<z
<ₗ-transitive {x :: xs} {.x :: ys} {.x :: zs} (inr (refl .x , xs<ys)) (inr (refl .x , ys<zs)) = inr ((refl x) , (<ₗ-transitive xs<ys ys<zs))
```

## Question 5 - Dyck Words

The Dyck language, named after the German mathematician Walther von
Dyck, can be described by the following simple inductive type:

```agda
data Dyck : ℕ → Type where
  ● : Dyck 0
  _↑ : {n : ℕ} → Dyck n → Dyck (suc n)
  _↓ : {n : ℕ} → Dyck (suc n) → Dyck n
```

Elements of this type can be pictured as "mountains", with instances
of the `↑` constructor corresponding to ascending moves (which we will draw using `/`) and instances
of the `↓` constructor corresponding to descending moves (which we will draw using `\`).  For example,
the element

```agda
m : Dyck 0
m = ● ↑ ↑ ↓ ↓ ↑ ↓
```
would correspond to the picture:
```text
   /\
  /  \/\
```
while the element
```agda
n : Dyck 1
n = ● ↑ ↓ ↑ ↑ ↑ ↓ ↓ ↑ ↓
```
would correspond to
```text
    /\
   /  \/\
/\/
```
Note how the number `n` in the type `Dyck n` records how many unmatched
ascending moves remain at the end of the word and can equivalently be seen as
the final (i.e. rightmost in the above pictures) height of the moutain.

Consequently elements of `Dyck 0` are those which return all the way to the
baseline, though a typical element of `Dyck 0` may do so many times.  For
example:
```text
          /\
   /\    /  \
/\/  \/\/    \
```
Let us say that an element of `Dyck 0` is *indecomposable* if it returns to the
baseline exactly once. Every element of `Dyck 0` can be decomposed, then, into a
list of indecomposable elements.

For the example word above, this would result in the following list of
indecomposable words:
```text
                             /\
            /\              /  \
[  /\   ,  /  \  ,  /\  ,  /    \ ]
```

Implement this operation:
```agda
-- remove-last can never be implemented as you may end up with some Dyck with a negative n
-- remove-last : (n : ℕ) → Dyck (suc n) → Dyck n
-- remove-last zero (● ↑) = ●
-- remove-last (suc n) ((d ↑) ↑) = (remove-last n (d ↑)) ↑
-- remove-last zero ((d ↓) ↑) = {!(remove-last ? (d ↓)) ↑!}
-- remove-last (suc n₁) ((d ↓) ↑) = {!!}
-- remove-last n (d ↓) = {!!}

-- remove-last (● ↑) = ●
-- remove-last ((d ↓) ↑) = {!!}
-- remove-last (d ↓) = {!!}#

-- remove-last (● ↑) = ●
-- remove-last ((d ↑) ↑) = remove-last (d ↑)
-- remove-last ((d ↓) ↑) = remove-last (d ↓)
-- remove-last (d ↓) = remove-last d


-- This definition may end up working but is complicated
-- indecomposable : (d : Dyck 0) → Type
-- indecomposable ● = 𝟙 -- This case is trivialy indecomposable but it may worth being false cause we don't want an infinite list of ●
-- indecomposable ((● ↑) ↓) = 𝟙 -- This is the smallest non-empty true case being /\
-- indecomposable (((d ↓) ↑) ↓) = 𝟘 -- This is the smallest false case being \/\ and touching at least twice 
-- indecomposable ((d ↓) ↓) = {!!}



-- This function constructs a list of all dyck that are constructable by popping off the head element
-- e.g sub-dyck /\/\ gives the list [ empty , / , /\ , /\/ ]
sub-dyck : {n : ℕ} (d : Dyck n) → List (Σ m ꞉ ℕ , Dyck m)
sub-dyck {n} (d ↓) = ((suc n) , d) :: (sub-dyck d)
sub-dyck {0} ● = []
sub-dyck {suc n} (d ↑) = (n , d) :: (sub-dyck d)

-- This definition reads as saying that a Dyck is decomposable if all sub-dycks possible none of them are of the Dyck 0 i.e. they never touch the bottom again
indecomposable : (d : Dyck 0) → Type
indecomposable d = (n : ℕ)(d : Dyck n) → (n , d) ∈ sub-dyck d → ¬ (zero ≡ n)


decompose : Dyck 0 → List (Dyck 0)
decompose = {!!}
```

**Note**: It is somewhat more convenient to return the *reverse* of the pictured
  list, but we will not count the order in considering your solution.

For convenience, here are the Agda mode shortcuts for the Dyck word constructors:

```text
↑ = \u
↓ = \d
● = \ci
```

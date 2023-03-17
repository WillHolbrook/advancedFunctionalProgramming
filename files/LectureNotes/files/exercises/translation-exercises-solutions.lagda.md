Extra Translation Exercises

```agda
module exercises.translation-exercises-solutions where

open import prelude
open import Fin
open import List-functions
open import natural-numbers-functions
open import exercises.practice-test-solutions
```

For each statement, you want to define, in Agda, a type-valued function that translates the English statement. You *do not* need to prove the statement.
 
As an example, let's consider the question from the Practice Test:
```agdacode
For every list and function `f`, given any member `x` of the list, we have that `f(x)` is also a member of the `f`-mapped list.
```
 
This would be translated to the following definition:

```agdacode
mapped-membership : Type → Type → Type
mapped-membership X Y = (x : X) (xs : List X) (f : X → Y) → x ∈ xs → f x ∈ map f xs
```

1. If we reverse a list twice, we get back the original list.

```agda
twice-rev-list-eq-list : {X : Type} → Type
twice-rev-list-eq-list {X} = (xs : List X) → reverse (reverse xs) ≡ xs
```

or, alternatively,

```agda
twice-rev-list-eq-listᵢ : {X : Type} → Type
twice-rev-list-eq-listᵢ {X} = is-idempotent (reverse {X})
```

2. If we map a function to a list, the resulting list will have the same length as the original list.

```agda
len-map-list-eq-len-list : {X Y : Type} → Type
len-map-list-eq-len-list {X} {Y} = (xs : List X) (f : X → Y) → length (map f xs) ≡ length xs
```
	
3. If we add a new head to a list, the length of the resulting list will be one plus the length of the original list.

```agda
len-prepend-list-equals-len-list-plus-one : {X : Type} → Type
len-prepend-list-equals-len-list-plus-one {X} = (xs : List X) (x : X) → length (x :: xs) ≡ suc (length xs)
```
	
4. If we sort a list (say of natural numbers), its length will be the same as that of the original list.

```agda
open import strict-total-order
open import sorting

len-sort-list-eq-len-list : {X : Type} → (τ : StrictTotalOrder X) → SortingAlgorithm τ → Type
len-sort-list-eq-len-list {X} τ θ = (xs : List X) → length (sort xs) ≡ length xs
  where open SortingAlgorithm θ
```
	
If we sort a list twice, this is the same as sorting it once.

```agda
sort-sort-list-eq-sort-list : {X : Type} → (τ : StrictTotalOrder X) → SortingAlgorithm τ → Type
sort-sort-list-eq-sort-list {X} τ θ = is-idempotent sort
  where open SortingAlgorithm θ
```


	
If we filter a list, the resulting list has a smaller-or-equal length.

```agda
filter : {A : Type} → (A → Bool) → List A → List A
filter p []        = []
filter p (x :: xs) = if (p x) then x :: ys else ys
 where
  ys = filter p xs
   
len-filter-list-lteq-len-list : {X : Type} → Type
len-filter-list-lteq-len-list {X} = (xs : List X) (p : X → Bool) → length (filter p xs) ≤ length xs
```
	
If we filter a list twice with the same predicate, this gives the same thing as filtering it once with that predicate.

```agda
filter-filter-list-eq-filter-list : {X : Type} → Type
filter-filter-list-eq-filter-list {X} = (p : X → Bool) → is-idempotent (filter p)
```
	
Every element that occurs in a list also occurs in the sorted list. (Use the \in function defined in the practice test.)

```agda
every-element-in-list-in-sorted-list : {X : Type} → (τ : StrictTotalOrder X) → SortingAlgorithm τ → Type
every-element-in-list-in-sorted-list {X} τ θ = (xs : List X) (x : X) → x ∈ xs → x ∈ sort xs
  where open SortingAlgorithm θ
```
	
Every element that occurs in a list after sorting it already occurs in the given list.

```agda
every-element-in-sorted-list-in-list : {X : Type} → (τ : StrictTotalOrder X) → SortingAlgorithm τ → Type
every-element-in-sorted-list-in-list {X} τ θ = (xs : List X) (x : X) → x ∈ sort xs → x ∈ xs
  where open SortingAlgorithm θ
```
	
It doesn't make a difference if we first filter and then sort, or if we first sort and then filter.
(It does make a difference in terms of performance, though - which order is more efficient?)

```agda
filter-sort-eq-sort-filter : {X : Type} → (τ : StrictTotalOrder X) → SortingAlgorithm τ → Type
filter-sort-eq-sort-filter {X} τ θ = (xs : List X) (p : X → Bool) → filter p (sort xs) ≡ sort (filter p xs)
  where open SortingAlgorithm θ
```
	
A function f : X → Y is called injective if f x = f y implies x = y.

```agda
is-injective : {X Y : Type} (f : X → Y) → Type
is-injective {X} {Y} f = (x y : X) → f x ≡ f y → x ≡ y
```
	
It is called surjective if for every y : Y there is some x with f x = y.

```agda
is-surjective : {X Y : Type} (f : X → Y) → Type
is-surjective {X} {Y} f = (y : Y) → Σ x ꞉ X , f x ≡ y

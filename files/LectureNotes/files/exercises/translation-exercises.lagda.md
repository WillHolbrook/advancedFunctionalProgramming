Extra Translation Exercises
```agda
module exercises.translation-exercises where

open import prelude
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

If we reverse a list twice, we get back the original list.

```agda
twice-rev-list-eq-list : Type
twice-rev-list-eq-list = {!!}
```
	
If we map a function to a list, the resulting list will have the same length as the original list.

```agda
len-map-list-eq-len-list : Type
len-map-list-eq-len-list = {!!}
```
	
If we add a new head to a list, the length of the resulting list will be one plus the length of the original list.

```agda
len-prepend-list-equals-len-list-plus-one : Type
len-prepend-list-equals-len-list-plus-one = {!!}
```
	
If we sort a list (say of natural numbers), its length will be the same as that of the original list.

```agda
sort : {X : Type} → List X → List X
sort = {!!}

len-sort-list-eq-len-list : Type
len-sort-list-eq-len-list = {!!}
```
	
If we sort a list twice, this is the same as sorting it once.

```agda
sort-sort-list-eq-sort-list : Type
sort-sort-list-eq-sort-list = {!!}
```
	
If we filter a list, the resulting list has a smaller-or-equal lengt.

```agda
len-filter-list-lteq-len-list : Type
len-filter-list-lteq-len-list = {!!}
```
	
If we filter a list twice with the same predicate, this gives the same thing as filtering it once with that predicate.

```agda
filter-filter-list-eq-filter-list : Type
filter-filter-list-eq-filter-list = {!!}
```
	
Every element that occurs in a list also occurs in the sorted list. (Use the \in function defined in the practice test.)

```agda
data _∈_ {X : Type} : X → List X → Type where
  head-case : (x : X) (xs : List X) → x ∈ (x :: xs)
  tail-case : (x : X) (xs : List X) → x ∈ xs → (y : X) → x ∈ (y :: xs)

every-element-in-list-in-sorted-list : Type
every-element-in-list-in-sorted-list = {!!}
```
	
Every element that occurs in a list after sorting it already occurs in the given list.

```agda
every-element-in-sorted-list-in-list : Type
every-element-in-sorted-list-in-list = {!!}
```
	
It doesn't make a difference if we first filter and then sort, or if we first sort and then filter.
(It does make a difference in terms of performance, though - which order is more efficient?)

```agda
num-steps : Type → ℕ
num-steps = {!!}

filter-sort-faster-sort-filter : Type
filter-sort-faster-sort-filter = {!!}
```
	
A function f : X -> Y is called injective if f x = f y implies x = y.

```agda
is-injective : {A : Type} (F : A → Type) → Type
is-injective = {!!}
```
	
It is called surjective if for every y:Y there is some x with f x = y.

```agda
is-surjective : {A : Type} (F : A → Type) → Type
is-surjective = {!!}
```
	
Harder. The pigeonhole principle. If we put n pigeons into k holes, and n > k, then some hole will have more than one pigeon. Formalize this condition for functions f: Fin n -> Fin k, where we think of f as putting pigeons into holes.

```agda
data _<_ : ℕ → ℕ → Type where
  <-zero : {  y : ℕ} → 0 < suc y
  <-suc : {x y : ℕ} → x < y → suc x < suc y

pigeonhole-principle : Type
pigeonhole-principle = {! !}
```

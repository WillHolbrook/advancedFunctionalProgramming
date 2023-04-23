<!--
```agda
{-# OPTIONS --without-K --safe #-}

module my-insertion-sort-2 where 

open import prelude
open import isomorphisms
open import List-functions
open import iso-utils
open import strict-total-order
open import sorting
```
-->

## Insertion Sort

Our first sorting algorithm is called the *insertion sort*.  The idea
is quite simple: we will define a function `insert` which attempts to
add a new element to the list by starting at the head and asking, for
each element it encounters, whether the the given element is larger
than the head element or not.  If the given element is smaller, it
becomes the new head, while if it is larger (or equal) we continue
trying to insert it in the tail.  In this way, larger elements are
accumulated at the end of the list and smaller elements at the
beginning.  We obtain a sorting algorithm by repeatedly inserting the
elements of a given list into the empty list.

Let's now put this into action.  We begin with the insert function:

```agda
module InsertionSort (X : Type) (τ : StrictTotalOrder X) where
  open _IsPermutationOf_
  open StrictTotalOrder τ
  open _≅_

  -- Definition of insertion sort
  insert : X → List X → List X
  insert = {!!}
```

Now we write a simple auxillary algorithm to iteratively insert a list
of elements in another list.

```agda
  insert-all : List X → List X → List X
  insert-all = {!!}
```

And now we obtain our insertion sort by iteratively inserting the elements of
our list into the empty list.

```agda
  insertion-sort : List X → List X
  insertion-sort = {!!}
```

## Proving the insertion produces a sorted list

Our first task is to show that this process always produces a sorted
list.  As the algorithm was written in three steps, it makes sense to break
our proof into three lemmas, one for each of the previous functions.

The first lemma says that if we insert a single element into a sorted
list, the result remains sorted.

```agda
  insert-is-sorted : (x : X) (xs : List X) → Sorted τ xs → Sorted τ (insert x xs)
  insert-is-sorted = ?
```
As you can see, there is not much difficulty here, just an exhaustive analysis of the possible cases.

For the next step, we simply use the previous lemma and induction to
say that we can insert a whole list of elements to a sorted list, and
the result remains sorted.  The fact that insertion sort produces a
sorted list is then just a special case:

```agda
  insert-all-is-sorted : (xs ys : List X) (ys-srtd : Sorted τ ys)
    → Sorted τ (insert-all xs ys)
  insert-all-is-sorted = ?

  insertion-sort-is-sorted : (xs : List X) → Sorted τ (insertion-sort xs)
  insertion-sort-is-sorted = ?
```

## Constructing the Permutation

Our next step is to construct a permutation for the sorted list.  To
do so, we will make use of some auxilliary isomorphisms defined
[here](iso-utils.lagda.md).

```agda
  insert-pos-iso : (x : X) (xs : List X)
    → Pos (insert x xs) ≅ 𝟙 ∔ Pos xs
  insert-pos-iso = ?
  
  insert-all-pos-iso : (xs ys : List X)
    → Pos (insert-all xs ys) ≅ Pos (xs ++ ys)
  insert-all-pos-iso = ?
```

Now we have to show that the inhabitants are preserved by our choice
of permutation.  The first lemma here shows how inhabitants interact
with the swapping isomorphism used above.

```agda
  pos-swap-lemma : (x y : X) (xs : List X)
    → (p : Pos (y :: xs))
    → Inhab (x :: y :: xs) (inr p) ≡
      Inhab (y :: x :: xs) (bijection (∔-left-swap-iso 𝟙 𝟙 (Pos xs)) (inr p))
  pos-swap-lemma = ?
```

With the above lemma, we can complete the calculation of the equality
of inhabitants with respect to the insert function.

```agda
  insert-inhab-eq : (x : X) (xs : List X)
    → (p : Pos (insert x xs))
    → Inhab (insert x xs) p ≡ Inhab (x :: xs) (bijection (insert-pos-iso x xs) p)
  insert-inhab-eq = ?
```

After a quick lemma showing how to extend a collection of inhabitant
equalities when adding a new element, we can show that inhabitants are
preserved by the permutation produced above for the insert-all
function.

```agda
  inhab-ext-lemma : (x : X) (xs ys : List X) 
    → (α : Pos xs ≅ Pos ys)
    → (e : (p : Pos xs) → Inhab xs p ≡ Inhab ys (bijection α p))
    → (p : Pos (x :: xs))
    → Inhab (x :: xs) p ≡ Inhab (x :: ys) (bijection (∔-pair-iso (id-iso 𝟙) α) p)
  inhab-ext-lemma = ?

  insert-all-inhab-eq : (xs ys : List X) (p : Pos (insert-all xs ys))
    → Inhab (insert-all xs ys) p ≡
      Inhab (xs ++ ys) (bijection (insert-all-pos-iso xs ys) p)
  insert-all-inhab-eq = ?
```

Together the previous functions give the data required to inhabit our
definition of `IsPermutationOf`.

```agda
  insert-is-perm : (x : X) (xs : List X)
    → (insert x xs) IsPermutationOf (x :: xs)
  pos-iso (insert-is-perm x xs) = insert-pos-iso x xs
  inhab-eq (insert-is-perm x xs) = insert-inhab-eq x xs

  insert-all-is-perm : (xs ys : List X)
    → (insert-all xs ys) IsPermutationOf (xs ++ ys)
  pos-iso (insert-all-is-perm xs ys) = insert-all-pos-iso xs ys
  inhab-eq (insert-all-is-perm xs ys) = insert-all-inhab-eq xs ys

  insertion-sort-is-perm : (xs : List X)
    → (insertion-sort xs) IsPermutationOf xs
  insertion-sort-is-perm xs = 
     transport (insertion-sort xs IsPermutationOf_)
       ([]-right-neutral xs) (insert-all-is-perm xs [])
```

And there we have it!  We can now wrap up all the work we have done
into our definition of sorting algorithm:

```agda
  insertion-sort-algorithm : SortingAlgorithm τ
  insertion-sort-algorithm =
    record { sort = insertion-sort
           ; sort-is-sorted = insertion-sort-is-sorted
           ; sort-is-permutation = insertion-sort-is-perm
           } 
```

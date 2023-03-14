# Lab 7 - Lab Exercises

```agda
module exercises.my-lab7 where

open import prelude
open import isomorphisms
open import natural-numbers-functions
open import Fin
open import Vector
open import List-functions
```

## Part I: Isomorphisms

### Exercise 1.1

**Prove** the following isomorphism:

```agda
×-distributivity-+ : (X Y Z : Type) → (X ∔ Y) × Z ≅ (X × Z) ∔ (Y × Z)
×-distributivity-+ X Y Z = record { bijection = f ; bijectivity = f-is-bijection }
 where
  f : (X ∔ Y) × Z → (X × Z) ∔ (Y × Z)
  f (inl x , z) = inl (x , z)
  f (inr y , z) = inr (y , z)

  g : (X × Z) ∔ (Y × Z) → (X ∔ Y) × Z
  g (inl (x , z)) = (inl x) , z
  g (inr (y , z)) = (inr y) , z

  gf : g ∘ f ∼ id
  gf (inl x , z) = refl (inl x , z)
  gf (inr y , z) = refl (inr y , z)

  fg : f ∘ g ∼ id
  fg (inl (x , z)) = refl (inl (x , z))
  fg (inr (y , z)) = refl (inr (y , z))

  f-is-bijection : is-bijection f
  f-is-bijection = record { inverse = g ; η = gf ; ε = fg }

```

### Exercise 1.2

We now define a function `alternate` that takes two types `X` and `Y` and
evaluates to `X` on `true` and evaluates to `Y` on `false`.

```agda
alternate : Type → Type → Bool → Type
alternate X _ true  = X
alternate _ Y false = Y
```

It can be proved that `Σ b ꞉ Bool , alternate X Y b` is the same thing as `X ∔
Y`. **Prove** this by constructing the following isomorphism:

```agda
∔-isomorphic-to-Σ-bool : (X Y : Type) → (X ∔ Y) ≅ (Σ b ꞉ Bool , alternate X Y b)
∔-isomorphic-to-Σ-bool X Y = record { bijection = f ; bijectivity = f-is-bijection }
 where
  f : X ∔ Y → (Σ b ꞉ Bool , alternate X Y b)
  f (inl x) = true , x
  f (inr y) = false , y

  g : ((Σ b ꞉ Bool , alternate X Y b)) → X ∔ Y
  g (true , x) = inl x
  g (false , y) = inr y

  gf : g ∘ f ∼ id
  gf (inl x) = refl (inl x)
  gf (inr y) = refl (inr y)

  fg : f ∘ g ∼ id
  fg (true , x) = refl (true , x)
  fg (false , y) = refl (false , y)

  f-is-bijection : is-bijection f
  f-is-bijection = record { inverse = g ; η = gf ; ε = fg }

```

### Exercise 1.3

**Prove** the following isomorphism:

```agda
sigma-curry-iso : (X Y : Type)
                → (A : X → Y → Type)
                → (Σ x ꞉ X , Σ y ꞉ Y , A x y) ≅ (Σ (x , y) ꞉ X × Y , A x y)
sigma-curry-iso X Y A = record { bijection = f ; bijectivity = f-is-bijection }
 where
  f : (Σ x ꞉ X , Σ y ꞉ Y , A x y) → (Σ (x , y) ꞉ X × Y , A x y)
  f (x , (y , Axy)) = (x , y) , Axy

  g : ((Σ (x , y) ꞉ X × Y , A x y)) → (Σ x ꞉ X , Σ y ꞉ Y , A x y)
  g ((x , y) , Axy) = x , (y , Axy)

  gf : g ∘ f ∼ id
  gf (x , (y , Axy)) = refl (x , y , Axy)

  fg : f ∘ g ∼ id
  fg ((x , y) , Axy) = refl ((x , y) , Axy)

  f-is-bijection : is-bijection f
  f-is-bijection = record { inverse = g ; η = gf ; ε = fg }
```


## Part II: Proving correctness of efficient Fibonacci

In Functional Programming you saw two ways of defining the Fibonacci function.
The first one, `fib` was fairly simple, but inefficient

```agda
fib : ℕ → ℕ
fib 0             = 0
fib 1             = 1
fib (suc (suc n)) = fib n + fib (suc n)
```

Therefore, we introduce a second version, `fib-fast`, which uses an accumulating
parameter to make it more efficient.

```agda
fib-aux : ℕ → ℕ → ℕ → ℕ
fib-aux a b 0       = b
fib-aux a b (suc n) = fib-aux (b + a) a n

fib-fast : ℕ → ℕ
fib-fast = fib-aux 1 0
```

It is not obvious, however, that `fib-fast` implements the same behaviour as
`fib`. In Agda, we can *prove* this, showing that `fib-fast` is correct.

The following lemma relates `fib-aux` and `fib` and is fundamental in proving
the correctness of `fib-fast`. You will be asked to prove it later.

```agda
fib-aux-fib-lemma : (k n : ℕ) → fib-aux (fib (suc n)) (fib n) k ≡ fib (k + n)
fib-aux-fib-lemma zero n = refl (fib n)
fib-aux-fib-lemma (suc k) n = 
  fib-aux (fib n + fib (suc n)) (fib (suc n)) k ≡⟨ fib-aux-fib-lemma k (suc n) ⟩
  fib (k + suc n)                               ≡⟨ ap fib (+-step k n) ⟩
  fib (suc (k + n))                             ∎
```

### Exercise 2.1

Using `fib-aux-fib-lemma`, **prove** the correctness of `fib-fast`.

```agda
right-unit : (n : ℕ) → n + 0 ≡ n
right-unit zero = refl zero
right-unit (suc n) = ap suc (right-unit n)

fib-fast-is-correct : (n : ℕ) → fib-fast n ≡ fib n
fib-fast-is-correct n =
  fib-fast n    ≡⟨ refl _ ⟩
  fib-aux 1 0 n ≡⟨ fib-aux-fib-lemma n 0 ⟩
  fib (n + 0)   ≡⟨ ap fib (right-unit n) ⟩
  fib n         ∎
```

*Hints*:
1. The lemma allows you to prove this fairly directly. There is no need to do
induction on `n`.
1. You may also find the `+-base` function from the
[natural-numbers-functions](../natural-numbers-functions.lagda.md) module useful.

### Exercise 2.2

Now **complete** the proof of fundamental lemma `fib-aux-fib-lemma` above.

*Hint*: You will probably want to use `+-step` from
[natural-numbers-functions](../natural-numbers-functions.lagda.md) at some
point.

### References

The exercises and solutions of Part 2 were based on [Neil Mitchell's
proof][mitchell] in the programming language [Idris][idris].

[mitchell]: http://neilmitchell.blogspot.com/2017/05/proving-fib-equivalence.html
[idris]: https://en.wikipedia.org/wiki/Idris_(programming_language)

## Part III: Inductive and Recursive Predicates and Relations

In the following sequence of exercises, we will practice writing
predicates and relations both inductively and recursively.

### Exercise 3.1

Define the strict order relation (i.e. m < n) on the natural numbers.
Do this both as an inductive predicate by adding constructors to the
following skeleton:

```agda
data _<_ : ℕ → ℕ → Type where
  <-zero : {  y : ℕ} → 0 < suc y
  <-suc : {x y : ℕ} → x < y → suc x < suc y

<-asymmetric : {x y : ℕ} → x < y → ¬ (y < x)
<-asymmetric {.0} {.(suc _)} <-zero ()
<-asymmetric {suc x} {suc y} (<-suc prf) (<-suc prf2) = <-asymmetric prf prf2
```

and now as a recursive definition:

```agda
_<'_ : ℕ → ℕ → Type
x     <' zero  = 𝟘
zero  <' suc y = 𝟙
suc x <' suc y = x <' y
```

### Exercise 3.2

Define a predicate `is-<-inc` on lists of natural numbers which states
that adjacent elements of the list are strictly increasing.  That is,
we should be able to prove `is-<-inc (2 :: 4 :: 7 :: [])` but *not*
`is-<-inc (4 :: 2 :: 7 [])`.  Do this both as an inductive and recursive
definition:

```agda
data is-<-inc : List ℕ → Type where
  []-is-<-inc : is-<-inc []
  append-empty-is-<-inc : (x : ℕ) → is-<-inc (x :: [])
  append-non-empty-is-<-inc : (x n : ℕ) (ns : List ℕ)
    → is-<-inc (n :: ns)
    → x < n
    → is-<-inc (x :: n :: ns)

-- func : (7 : ℕ) -...... 
is-<-inc' : List ℕ → Type
is-<-inc' [] = 𝟙
is-<-inc' (x :: []) = 𝟙
is-<-inc' (x :: y :: ns) = is-<-inc' (y :: ns) × (x < y)
-- with x <' x₁
-- is-<-inc' (x :: x₁ :: ns) | a = {!!}

contra : is-<-inc' (4 :: 2 :: 7 :: []) → 𝟘
-- contra (_ , <-suc (<-suc ()))
contra (_ , 4<2) = <-asymmetric (<-suc (<-suc <-zero)) 4<2
```

### Exercise 3.3

Define a relations `_<-all_ :: ℕ → List ℕ → Type` and `_all-<_ :: List
ℕ → ℕ → Type` expressing that the given natural number is less than all
the elements of the given list or, respectively, that every element of
a list is less than some give element.  For example we should have:

`7 <-all (10 :: 14 :: 23 :: [])`

`(2 :: 1 :: 4 :: []) all-< 10`

```agda
data _<-all_ : ℕ → List ℕ → Type where
  any-<-all-[] : (n : ℕ) → n <-all []
  prepend-<-all : {b : ℕ}(n : ℕ)(ns : List ℕ)
    → b <-all ns
    → b < n
    → b <-all (n :: ns)
  
_<-all'_ : ℕ → List ℕ → Type
x <-all' [] = 𝟙
x <-all' (y :: xs) = x < y × x <-all' xs

check : 7 <-all (10 :: 14 :: 23 :: [])
check = prepend-<-all 10 (14 :: 23 :: [])
          (prepend-<-all 14 (23 :: [])
           (prepend-<-all 23 [] (any-<-all-[] 7)
            (<-suc (<-suc (<-suc (<-suc (<-suc (<-suc (<-suc <-zero))))))))
           (<-suc (<-suc (<-suc (<-suc (<-suc (<-suc (<-suc <-zero))))))))
          (<-suc (<-suc (<-suc (<-suc (<-suc (<-suc (<-suc <-zero)))))))

check' : ¬ (11 <-all (10 :: 14 :: 23 :: []))
check' (prepend-<-all .10 .(14 :: 23 :: [])
  a
  (<-suc (<-suc (<-suc (<-suc (<-suc (<-suc (<-suc (<-suc (<-suc (<-suc ())))))))))))

check''' : 7 <-all' (10 :: 14 :: 23 :: [])
check''' = <-suc (<-suc (<-suc (<-suc (<-suc (<-suc (<-suc <-zero)))))) ,
             <-suc (<-suc (<-suc (<-suc (<-suc (<-suc (<-suc <-zero)))))) ,
             <-suc (<-suc (<-suc (<-suc (<-suc (<-suc (<-suc <-zero)))))) , ⋆

check'''' : ¬ (11 <-all' (10 :: 14 :: 23 :: []))
check'''' (<-suc (<-suc (<-suc (<-suc (<-suc (<-suc (<-suc (<-suc (<-suc (<-suc ()))))))))) , _)

data _all-<_ : List ℕ → ℕ → Type where
  
_all-<'_ : List ℕ → ℕ → Type
xs all-<' x = {!!}
```

and so on.  Again, express these predicates both inductively and
recursively.

### Exercise 3.4

Using the predicates you have defined above, state and prove the
following: if `ns : List ℕ` is an increasing list and `n : ℕ` is a
natural number less than every element of the list, then `(n :: ns)`
is also an increasing list.

### Exercise 3.5

A function `f : ℕ → ℕ` is said to be monotone if it
preserves the _<_ relation.  Define the predicate of being a monotone function.

```agda
is-monotone : {!!}
is-monotone = {!!} 
```

State and prove that if `ns : List ℕ` is an increasing list, then for any
monotone function `f`, `map f ns` is *also* an increasing list.

### Exercise 3.6

Consider the type of binary trees with nodes labeled by the elements
of some type `X`:

```agda
data Bin (X : Type) : Type where
  lf : Bin X 
  nd : X → Bin X → Bin X → Bin X
```

In analogy with the case of lists above, define predicates
`_<-all-Bin_ : ℕ → Bin ℕ → Type` and `_all-<-Bin_ : Bin ℕ → ℕ → Type`
(both inductively and recursively) stating that a given element `n :
ℕ` is less than (respectively greater than) every element appearing in
some binary tree of natural numbers.

### Exercise 3.7

Use the relations of the previous exercise to define a predicate
`is-bst : Bin ℕ → Type` stating that a given tree is a [binary search
tree](https://en.wikipedia.org/wiki/Binary_search_tree).

Additionally define the *type* of all binary search trees.

```agda
BST : Type
BST = {!!} 
```

### Exercise 3.8 - Hard!!

To complete this exercise, you will need to use all the material
above, and possibly additional definitions and lemmas.  So while the
result is intuitively clear, it will take some work to finish. Try to
break it into steps which seem clear to you and work on the individual
steps.  Be creative!

Consider the function:

```agda
flatten : Bin ℕ → List ℕ
flatten lf = []
flatten (nd n l r) = flatten l ++ (n :: flatten r) 
```

taking a tree to its list of nodes.  State and prove that if the input
tree is a binary search tree, then the result is an increasing list.

## Part IV: Making statements as types:

You can use all of the following statements to practice writing
predicates and theorems as types.  You may wish to try proving some of
the statements.

1. If we reverse a list twice, we get back the original list.
2. If we map a function to a list, the resulting list will have the same length as the original list.
3. If we add a new head to a list, the length of the resulting list will be one plus the length of the original list.
4. If we sort a list (say of natural numbers), its length will be the same as that of the original list.
5. If we sort a list twice, this is the same as sorting it once.
6. If we filter a list, the resulting list has a smaller-or-equal length.
7. If we filter a list twice with the same predicate, this gives the same thing as filtering it once with that predicate.
8. Every element that occurs in a list also occurs in the sorted list. (Use the \in function defined in the practice test.)
9. Every element that occurs in a list after sorting it already occurs in the given list.
10. It doesn't make a difference if we first filter and then sort, or if we first sort and then filter. (It does make a difference in terms of performance, though - which order is more efficient?)
11. A function f : X -> Y is called injective if f x = f y implies x = y.  Define the predicate of being injective.
12. It is called surjective if for every y:Y there is some x with f x = y.  Define the predicate of being surjective.
13. Harder. The pigeonhole principle. If we put n pigeons into k holes, and n > k, then some hole will have more than one pigeon. Formalize this condition for functions f: Fin n -> Fin k, where we think of f as putting pigeons into holes.

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
  []-all-<-any : (n : ℕ) → [] all-< n
  prepend-all-< : {b : ℕ}(n : ℕ){ns : List ℕ}
    → ns all-< b
    → n < b
    → (n :: ns) all-< b
  
_all-<'_ : List ℕ → ℕ → Type
[] all-<' b = 𝟙
(x :: xs) all-<' b = (x < b) × (xs all-<' b)

check₁ : (10 :: 14 :: 23 :: []) all-< 24
check₁ = prepend-all-< 10
           (prepend-all-< 14
            (prepend-all-< 23 ([]-all-<-any 24)
             (<-suc
              (<-suc
               (<-suc
                (<-suc
                 (<-suc
                  (<-suc
                   (<-suc
                    (<-suc
                     (<-suc
                      (<-suc
                       (<-suc
                        (<-suc
                         (<-suc
                          (<-suc
                           (<-suc
                            (<-suc
                             (<-suc
                              (<-suc
                               (<-suc (<-suc (<-suc (<-suc (<-suc <-zero))))))))))))))))))))))))
            (<-suc
             (<-suc
              (<-suc
               (<-suc
                (<-suc
                 (<-suc
                  (<-suc
                   (<-suc
                    (<-suc (<-suc (<-suc (<-suc (<-suc (<-suc <-zero)))))))))))))))
           (<-suc
            (<-suc
             (<-suc
              (<-suc (<-suc (<-suc (<-suc (<-suc (<-suc (<-suc <-zero))))))))))

check₁' : ¬ ((10 :: 14 :: 23 :: []) all-< 11)
check₁' (prepend-all-< .10 (prepend-all-< .14 a (<-suc (<-suc (<-suc (<-suc (<-suc (<-suc (<-suc (<-suc (<-suc (<-suc (<-suc ())))))))))))) x)

check₁''' : (10 :: 14 :: 23 :: []) all-<' 24
check₁''' = <-suc
              (<-suc
               (<-suc
                (<-suc (<-suc (<-suc (<-suc (<-suc (<-suc (<-suc <-zero)))))))))
              ,
              <-suc
              (<-suc
               (<-suc
                (<-suc
                 (<-suc
                  (<-suc
                   (<-suc
                    (<-suc
                     (<-suc (<-suc (<-suc (<-suc (<-suc (<-suc <-zero)))))))))))))
              ,
              <-suc
              (<-suc
               (<-suc
                (<-suc
                 (<-suc
                  (<-suc
                   (<-suc
                    (<-suc
                     (<-suc
                      (<-suc
                       (<-suc
                        (<-suc
                         (<-suc
                          (<-suc
                           (<-suc
                            (<-suc
                             (<-suc
                              (<-suc
                               (<-suc (<-suc (<-suc (<-suc (<-suc <-zero))))))))))))))))))))))
              , ⋆

check₁'''' : ¬ ((10 :: 14 :: 23 :: []) all-<' 11)
check₁'''' (_ , (<-suc (<-suc (<-suc (<-suc (<-suc (<-suc (<-suc (<-suc (<-suc (<-suc (<-suc ()))))))))))) , _)
```

and so on.  Again, express these predicates both inductively and
recursively.

### Exercise 3.4

Using the predicates you have defined above, state and prove the
following: if `ns : List ℕ` is an increasing list and `n : ℕ` is a
natural number less than every element of the list, then `(n :: ns)`
is also an increasing list.

```agda
prepend-smaller-element-preserves-increasing : (n : ℕ)(ns : List ℕ)
  → is-<-inc ns
  → n <-all ns
  → is-<-inc (n :: ns)
prepend-smaller-element-preserves-increasing n [] inc less = append-empty-is-<-inc n
prepend-smaller-element-preserves-increasing n (x :: ns) inc (prepend-<-all .x .ns less n<x) = append-non-empty-is-<-inc n x ns inc n<x
```

### Exercise 3.5

A function `f : ℕ → ℕ` is said to be monotone if it
preserves the _<_ relation.  Define the predicate of being a monotone function.

```agda
is-monotone : (f : ℕ → ℕ) → Type
is-monotone f = (x y : ℕ) → x < y → f x < f y

inc-map-mono-is-inc : (ns : List ℕ)(f : ℕ → ℕ)
  → is-<-inc ns
  → is-monotone f
  → is-<-inc (map f ns)
inc-map-mono-is-inc [] f inc mono = inc
inc-map-mono-is-inc (x :: []) f inc mono = append-empty-is-<-inc (f x)
inc-map-mono-is-inc (x :: x₁ :: ns) f (append-non-empty-is-<-inc .x .x₁ .ns inc x₂) mono = append-non-empty-is-<-inc (f x) (f x₁) (map f ns) (inc-map-mono-is-inc (x₁ :: ns) f inc mono) (mono x x₁ x₂)
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

data _<-all-Bin_ : ℕ → Bin ℕ → Type where
  lf-<-all : {b : ℕ} → b <-all-Bin lf
  nd-<-all : {b : ℕ}(n : ℕ)(l r : Bin ℕ)
    → b <-all-Bin l
    → b <-all-Bin r
    → b < n
    → b <-all-Bin (nd n l r)
  

_<-all-Bin'_ : ℕ → Bin ℕ → Type
b <-all-Bin' lf = 𝟙
b <-all-Bin' nd x l r = b < x × (b <-all-Bin' l ) × (b <-all-Bin' r)

data _all-<-Bin_ : Bin ℕ → ℕ → Type where
  lf-all-< : {b : ℕ} → lf all-<-Bin b
  nd-all-< : {b : ℕ}(n : ℕ)(l r : Bin ℕ)
    → l all-<-Bin b
    → r all-<-Bin b
    → n < b
    → (nd n l r) all-<-Bin b
 
_all-<-Bin'_ : Bin ℕ → ℕ → Type
lf all-<-Bin' b = 𝟙
(nd x l r) all-<-Bin' b = x < b × l all-<-Bin' b × r all-<-Bin' b
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
data is-bst : Bin ℕ → Type where
  lf-is-bst : is-bst lf
  nd-is-bst : (x : ℕ)(l r : Bin ℕ)
    → l all-<-Bin x
    → x <-all-Bin r
    → is-bst l
    → is-bst r
    → is-bst (nd x l r)

is-bst' : Bin ℕ → Type
is-bst' lf = 𝟙
is-bst' (nd x l r) = l all-<-Bin x × x <-all-Bin r × is-bst' l × is-bst' r

BST : Type
BST = Σ b ꞉ Bin ℕ , is-bst b 
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

all-<-prepend : {b : ℕ}(y : ℕ)(xs : List ℕ)
  → (y :: xs) all-< b
  → xs all-< b
all-<-prepend {b} y [] allxs = []-all-<-any b
all-<-prepend {b} y (x :: xs) (prepend-all-< .y (prepend-all-< .x allxs x<b) y<b)
  = prepend-all-< x allxs x<b

inc-lemma : (xs ys : List ℕ)(n : ℕ)
  → xs all-< n
  → n <-all ys
  → is-<-inc xs
  → is-<-inc ys
  → is-<-inc (xs ++ (n :: ys))
inc-lemma [] [] n xsless lessys incxs incys
  = append-empty-is-<-inc n
inc-lemma [] (y :: ys) n xsless (prepend-<-all .y .ys lessys n<y) incxs incys
  = append-non-empty-is-<-inc n y ys incys n<y
inc-lemma (x :: []) [] n (prepend-all-< .x xsless x<n) lessys incxs incys
  = append-non-empty-is-<-inc x n [] (append-empty-is-<-inc n) x<n
inc-lemma (x :: []) (y :: ys) n (prepend-all-< .x xsless x<n) (prepend-<-all .y .ys lessys n<y) incxs incys
  = append-non-empty-is-<-inc x n (y :: ys) (append-non-empty-is-<-inc n y ys incys n<y) x<n
inc-lemma (x :: x₁ :: xs) ys n xsless lessys (append-non-empty-is-<-inc .x .x₁ .xs incxs x<x₁) incys
  = append-non-empty-is-<-inc x x₁ (xs ++ (n :: ys)) IH x<x₁
  where
    IH : is-<-inc (x₁ :: xs ++ (n :: ys))
    IH = inc-lemma (x₁ :: xs) ys n (all-<-prepend x (x₁ :: xs) xsless) lessys incxs incys

all-<-++ : {b : ℕ}(xs ys : List ℕ) → xs all-< b → ys all-< b → (xs ++ ys) all-< b
all-<-++ {b} [] ys allxs allys = allys
all-<-++ {b} (x :: xs) ys (prepend-all-< .x allxs x<b) allys
  = prepend-all-< x (all-<-++ xs ys allxs allys) x<b

all-<-Bin-imp-all-< : {b : ℕ}(bin : Bin ℕ) → bin all-<-Bin b → (flatten bin) all-< b
all-<-Bin-imp-all-< {b} lf binless = []-all-<-any b
all-<-Bin-imp-all-< {b} (nd x l r) (nd-all-< .x .l .r lless rless x<b)
  = all-<-++ (flatten l) (x :: flatten r) IHL (prepend-all-< x IHR x<b)
  where
    IHL : flatten l all-< b
    IHL = all-<-Bin-imp-all-< l lless

    IHR : flatten r all-< b
    IHR = all-<-Bin-imp-all-< r rless

<-all-++ : {b : ℕ}(xs ys : List ℕ) → b <-all xs → b <-all ys → b <-all (xs ++ ys)
<-all-++ {b} [] ys allxs allys = allys
<-all-++ {b} (x :: xs) ys (prepend-<-all .x .xs allxs b<x) allys
  = prepend-<-all x (xs ++ ys) (<-all-++ xs ys allxs allys) b<x

<-all-Bin-imp-<-all : {b : ℕ}(bin : Bin ℕ) → b <-all-Bin bin → b <-all (flatten bin)
<-all-Bin-imp-<-all {b} lf binless = any-<-all-[] b
<-all-Bin-imp-<-all {b} (nd x l r) (nd-<-all .x .l .r lless rless b<x) = <-all-++ (flatten l) (x :: flatten r) IHL (prepend-<-all x (flatten r) (<-all-Bin-imp-<-all r rless) b<x)
  where
    IHL : b <-all (flatten l)
    IHL = <-all-Bin-imp-<-all l lless

    IHR : b <-all (flatten r)
    IHR = <-all-Bin-imp-<-all r rless

flattened-bst-is-inc : (bt : Bin ℕ) → is-bst bt → is-<-inc (flatten bt)
flattened-bst-is-inc lf bst = []-is-<-inc
flattened-bst-is-inc (nd x l r) (nd-is-bst .x .l .r l<x x<r bstl bstr) = inc-lemma (flatten l) (flatten r) x (all-<-Bin-imp-all-< l l<x) (<-all-Bin-imp-<-all r x<r) IHL IHR
  where
    IHL : is-<-inc (flatten l)
    IHL = flattened-bst-is-inc l bstl

    IHR : is-<-inc (flatten r)
    IHR = flattened-bst-is-inc r bstr 
```

taking a tree to its list of nodes.  State and prove that if the input
tree is a binary search tree, then the result is an increasing list.

## Part IV: Making statements as types:

You can use all of the following statements to practice writing
predicates and theorems as types.  You may wish to try proving some of
the statements.

If we reverse a list twice, we get back the original list.

```agda
twice-rev-list-eq-list : {X : Type} → Type
twice-rev-list-eq-list {X} = (xs : List X) → reverse (reverse xs) ≡ xs
```
	
If we map a function to a list, the resulting list will have the same length as the original list.

```agda
len-map-list-eq-len-list : {X Y : Type} → Type
len-map-list-eq-len-list {X} {Y} = (xs : List X)(f : X → Y) → length (map f xs) ≡ length xs
```
	
If we add a new head to a list, the length of the resulting list will be one plus the length of the original list.

```agda
len-prepend-list-equals-len-list-plus-one : {X : Type} → Type
len-prepend-list-equals-len-list-plus-one {X} = (xs : List X)(x : X) → length (x :: xs) ≡ 1 + length xs
```
	
If we sort a list (say of natural numbers), its length will be the same as that of the original list.

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
sort-sort-list-eq-sort-list {X} τ θ = (xs : List X) → sort (sort xs) ≡ sort xs
  where open SortingAlgorithm θ
```
	
If we filter a list, the resulting list has a smaller-or-equal lengt.

```agda
filter : {A : Type} → (A → Bool) → List A → List A
filter p []        = []
filter p (x :: xs) = if (p x) then x :: ys else ys
 where
  ys = filter p xs

len-filter-list-lteq-len-list : {X : Type} → Type
len-filter-list-lteq-len-list {X} = (xs : List X)(f : X → Bool) → length (filter f xs) ≤ length xs 
```
	
If we filter a list twice with the same predicate, this gives the same thing as filtering it once with that predicate.

```agda
filter-filter-list-eq-filter-list : {X : Type} → Type
filter-filter-list-eq-filter-list {X} = (xs : List X)(f : X → Bool) → filter f (filter f xs) ≡ filter f xs
```
	
Every element that occurs in a list also occurs in the sorted list. (Use the \in function defined in the practice test.)

```agda
data _∈_ {X : Type} : X → List X → Type where
  head-case : (x : X) (xs : List X) → x ∈ (x :: xs)
  tail-case : (x : X) (xs : List X) → x ∈ xs → (y : X) → x ∈ (y :: xs)

every-element-in-list-in-sorted-list : {X : Type} → (τ : StrictTotalOrder X) → SortingAlgorithm τ → Type
every-element-in-list-in-sorted-list {X} τ θ = (x : X)(xs : List X) → x ∈ xs → x ∈ sort xs
  where open SortingAlgorithm θ
```
	
Every element that occurs in a list after sorting it already occurs in the given list.

```agda
every-element-in-sorted-list-in-list : {X : Type} → (τ : StrictTotalOrder X) → SortingAlgorithm τ → Type
every-element-in-sorted-list-in-list {X} τ θ = (x : X)(xs : List X) → x ∈ sort xs → x ∈ xs
  where open SortingAlgorithm θ
```
	
It doesn't make a difference if we first filter and then sort, or if we first sort and then filter.
(It does make a difference in terms of performance, though - which order is more efficient?)

```agda
filter-sort-eq-sort-filter : {X : Type} → (τ : StrictTotalOrder X) → SortingAlgorithm τ → Type
filter-sort-eq-sort-filter {X} τ θ = (xs : List X)(f : X → Bool) → sort (filter f xs) ≡ filter f (sort xs)
  where open SortingAlgorithm θ
```
	
A function f : X -> Y is called injective if f x = f y implies x = y.

```agda
is-injective : {X Y : Type} (f : X → Y) → Type
is-injective {X} f = (x y : X) → f x ≡ f y → x ≡ y
```
	
It is called surjective if for every y:Y there is some x with f x = y.

```agda
is-surjective : {X Y : Type} (f : X → Y) → Type
is-surjective {X} {Y} f = (y : Y) → Σ x ꞉ X , f x ≡ y
```
	
Harder. The pigeonhole principle. If we put n pigeons into k holes, and n > k, then some hole will have more than one pigeon. Formalize this condition for functions f: Fin n -> Fin k, where we think of f as putting pigeons into holes.

```agda
pigeonhole-principle : Type
pigeonhole-principle = (n k : ℕ) → k < n → (f : Fin n → Fin k) → Σ (finn1 , finn2) ꞉ Fin n × Fin n , ¬ (finn1 ≡ finn2) × (f finn1 ≡ f finn2)
```

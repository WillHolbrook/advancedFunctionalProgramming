# Week 4 - Lab Sheet

```agda
module exercises.lab4 where
open import prelude
open import List-functions

private
```

## Part I: Reverse is an involution

We wish to prove that the `reverse` function on lists is an involution;
that is to say that reversing a list twice is the same as doing nothing.

### Exercise 1.1

First, we will prove the following lemma.

```agda
 reverse-lemma : {X : Type} (x : X) (xs : List X)
               → x :: reverse xs ≡ reverse (xs ++ [ x ])
 reverse-lemma = {!!}
```

**Prove** the lemma about `reverse`.

### Exercise 1.2

The following proof skeleton has been provided for you, using [notation for
equational reasoning][1].

```agda
 reverse-is-involution : {X : Type} → (xs : List X) → xs ≡ reverse (reverse xs)
 reverse-is-involution [] = {!!}
 reverse-is-involution (x :: xs)
  = x :: xs                       ≡⟨ {!!} ⟩
    x :: reverse (reverse xs)     ≡⟨ {!!} ⟩
    reverse (reverse xs ++ [ x ]) ≡⟨ {!!} ⟩
    reverse (reverse (x :: xs))   ∎
```

**Fill** the holes of our proof that `reverse` is an involution.

## Part II: Associativity of addition of natural numbers

We wish to prove the associativity of `_+_` on the natural numbers.

```agda
 +-assoc : (x y z : ℕ) → x + (y + z) ≡ (x + y) + z
 +-assoc = {!!}
```

**Complete** the proof that `_+_` is associative.

## Part III: Order on the natural numbers

In this part we will study two ways of expressing that a natural number is less
than or equal to another natural number.

The first definition is an inductive one.

```agda
 data _≤_ : ℕ → ℕ → Type where
  ≤-zero : (  y : ℕ) → 0 ≤ y
  ≤-suc  : (x y : ℕ) → x ≤ y → suc x ≤ suc y
```

It says:
1. that zero is less than or equal to any natural number;
1. if `x` is less than or equal to `y`, then `suc x` is less than or equal to `suc y`.

The second definition uses a `Σ`-type.

```agda
 _≤'_ : ℕ → ℕ → Type
 x ≤' y = Σ k ꞉ ℕ , x + k ≡ y
```

It says that `x` is less than or equal to `y` if we have some `k : ℕ`
such that `x + k ≡ y`.

We will prove that the two definitions are logically equivalent.

### Exercise 3.1

In order to prove that the first definition implies the second, we first
prove two little lemmas about `_≤'_`.

Note that they amount to the constructors of `_≤_`.

```agda
 ≤'-zero : (  y : ℕ) → 0 ≤' y
 ≤'-zero = {!!}

 ≤'-suc : (x y : ℕ) → x ≤' y → suc x ≤' suc y
 ≤'-suc = {!!}
```

**Prove** the two little lemmas about `_≤'_`.

### Exercise 3.2

We now prove that the first definition implies the second.

```agda
 ≤-prime : (x y : ℕ) → x ≤ y → x ≤' y
 ≤-prime = {!!}
```

**Prove** that `x ≤ y` implies `x ≤' y` using the little lemmas from 3.1.

### Exercise 3.3

The other direction is slightly trickier.

```agda
 ≤-unprime : (x y : ℕ) → x ≤' y → x ≤ y
 ≤-unprime = {!!}
```

**Prove** that `x ≤' y` implies `x ≤ y`.

*Hint:* The base case only requires pattern matching on `x`, whereas
the inductive case requires further pattern matching.

### Exercise 3.4

The order on the natural numbers is transitive, meaning that if
`x ≤ y` and `y ≤ z` then also `x ≤ z`. We can prove this for
both our definitions of the order.

```agda
 ≤-trans : (x y z : ℕ) → x ≤ y → y ≤ z → x ≤ z
 ≤-trans = {!!}

 ≤'-trans : (x y z : ℕ) → x ≤' y → y ≤' z → x ≤' z
 ≤'-trans = {!!}
```

**Complete** the proofs that `_≤_` and `_≤'_` are transitive.

## Part IV: Decidability and decidable equality

In last week's exercises, you constructed proofs of logical formulae by writing
Agda programs through the interpretation of Agda types as propositions. We
mentioned, however, that this interpretation does not make sense _a priori_ in
the setting of classical logic and we said that we have to work _constructively_
to make logical sense of Agda's types. More specifically, we mentioned in
[Exercise 2.3][0] that the logical interpretation of the law of excluded middle
`(A : Type) → A ∔ ¬ A`, is not provable in Agda.

Notice, however, that the statement

```txt
    (A : Type) → A ∔ ¬ A
```

is to be viewed as asserting that _the law of excluded middle holds for all
types_. Even though this fails to hold in the context of Agda's type system, it
doesn't mean that the law of excluded middle does not hold for _some_ types. In
this exercise, this is precisely the question that we will be interested in; we
will study “types that admit the law of excluded middle”. Such types are called
**decidable types**. We will express this notion through the Agda predicate
`is-decidable`:

```agda
 is-decidable : Type → Type
 is-decidable A = A ∔ ¬ A
```

To assert `is-decidable A` for some type `A` is to say that type `A` satisfies
the law of excluded middle: we can either construct an inhabitant of `A` or
prove that the existence of an inhabitant for `A` is impossible.

We can consider the decidability of any type but we will often be interested in
the _decidability of equality types_. A type `A` is said to have _decidable
equality_ iff for any two `x y : A`, the identity type `x ≡ y` is decidable. We
can write this notion down in Agda as follows:

```agda
 has-decidable-equality : Type → Type
 has-decidable-equality A = (x y : A) → is-decidable (x ≡ y)
```

### Exercise 4.1 (Harder!)

To familiarise yourself with the notion of decidable equality, **prove** that
the `Bool` type has decidable equality:

```agda
 bool-has-decidable-equality : has-decidable-equality Bool
 bool-has-decidable-equality = {!!}
```

### Exercise 4.2

Recall the following definitions of decidable predicates and "exhaustively searchable" types from
the [lecture notes](https://git.cs.bham.ac.uk/afp/afp-learning-2022-2023/-/blob/master/files/LectureNotes/files/decidability.lagda.md)

```agda
is-decidable-predicate : {X : Type} → (X → Type) → Type
is-decidable-predicate {X} A = (x : X) → is-decidable (A x)

is-exhaustively-searchable : Type → Type₁
is-exhaustively-searchable X = (A : X → Type)
                             → is-decidable-predicate A
                             → is-decidable (Σ x ꞉ X , A x)
```                              

Now, for each `n`, we can construct a type with exactly `n` elements as follows:

```agda
data Fin : ℕ → Type where
  zero : {n : ℕ} → Fin (suc n)
  succ : {n : ℕ} → Fin n → Fin (suc n)
```
(You can read more about this type [here](https://git.cs.bham.ac.uk/afp/afp-learning-2022-2023/-/blob/master/files/LectureNotes/files/Fin.lagda.md))

Show that `Fin n` is exhaustively searchable for every `n`.

```agda
Fin-is-exhaustively-searchable : (n : ℕ) → is-exhaustively-searchable (Fin n)
Fin-is-exhaustively-searchable = {!!} 
```

[0]: https://git.cs.bham.ac.uk/mhe/afp-learning/-/blob/main/files/LectureNotes/files/exercises/homework3.lagda.md#exercise-23
[1]: https://git.cs.bham.ac.uk/mhe/afp-learning/-/blob/main/files/LectureNotes/files/identity-type.lagda.md#notation-for-equality-reasoning

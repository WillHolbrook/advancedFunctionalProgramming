<!--
```agda
{-# OPTIONS --without-K --safe #-}

module isomorphisms where

open import prelude

```
-->
# Type isomorphisms

A function `f : A → B` is called a *bijection* if there is a function `g : B → A` in the opposite direction such that `g ∘ f ∼ id` and `f ∘ g ∼ id`. Recall that `_∼_` is [pointwise equality](identity-type.lagda.md) and that `id` is the [identity function](products.lagda.md). This means that we can convert back and forth between the types `A` and `B` landing at the same element with started with, either from `A` or from `B`. In this case, we say that the types `A` and `B` are *isomorphic*, and we write `A ≅ B`. Bijections are also called type *isomorphisms*. We can define these concepts in Agda using [sum types](sums.lagda.md) or [records](https://agda.readthedocs.io/en/latest/language/record-types.html). We will adopt the latter, but we include both definitions for the sake of illustration. Recall that we [defined](general-notation.lagda.md) the domain of a function `f : A → B` to be `A` and its codomain to be `B`.

Here we apply the proposition-as-types interpretation of logic to define the concepts:
<!--
```agda
module _ where
 private
```
-->
```agda
  is-bijection : {A B : Type} → (A → B) → Type
  is-bijection f = Σ g ꞉ (codomain f → domain f) , ((g ∘ f ∼ id) × (f ∘ g ∼ id))

  _≅_ : Type → Type → Type
  A ≅ B = Σ f ꞉ (A → B) , is-bijection f

test = true
```
And here we give an equivalent definition which uses records and is usually more convenient in practice and is the one we adopt:
```agda
record is-bijection {A B : Type} (f : A → B) : Type where
 constructor
  Inverse
 field
  inverse : B → A
  η       : inverse ∘ f ∼ id
  ε       : f ∘ inverse ∼ id

record _≅_ (A B : Type) : Type where
 constructor
  Isomorphism
 field
  bijection   : A → B
  bijectivity : is-bijection bijection

infix 0 _≅_

record _≅'_ (A B : Type) : Type where
  field
    f : A → B
    g : B → A
    l : (a : A) → g (f a) ≡ a
    r : (b : B) → f (g b) ≡ b

infix 0 _≅'_
```


The definition with `Σ` is probably more intuitive, but, as discussed above, the definition with a record is often easier to work with, because we can easily extract the components of the definitions using the names of the fields. It also often allows Agda to infer more types, and to give us more sensible goals in the interactive development of Agda programs and proofs.

Notice that `inverse` plays the role of `g`. The reason we use `inverse` is that then we can use the word `inverse` to extract the inverse of a bijection. Similarly we use `bijection` for `f`, as we can use the word `bijection` to extract the bijection from a record.

## Some basic examples

```agda
open import binary-type
open import Bool

Bool-𝟚-isomorphism : Bool ≅ 𝟚
Bool-𝟚-isomorphism = record { bijection = f ; bijectivity = f-is-bijection }
 where
  f : Bool → 𝟚
  f false = 𝟎
  f true  = 𝟏

  g : 𝟚 → Bool
  g 𝟎 = false
  g 𝟏 = true

  gf : g ∘ f ∼ id
  gf true  = refl true
  gf false = refl false

  fg : f ∘ g ∼ id
  fg 𝟎 = refl 𝟎
  fg 𝟏 = refl 𝟏

  f-is-bijection : is-bijection f
  f-is-bijection = Inverse g gf fg
```
But there is also a different isomorphism:
```agda
Bool-𝟚-isomorphism' : Bool ≅ 𝟚
Bool-𝟚-isomorphism' = record { bijection = f ; bijectivity = f-is-bijection }
 where
  f : Bool → 𝟚
  f false = 𝟏
  f true  = 𝟎

  g : 𝟚 → Bool
  g 𝟎 = true
  g 𝟏 = false

  gf : g ∘ f ∼ id
  gf true  = refl true
  gf false = refl false

  fg : f ∘ g ∼ id
  fg 𝟎 = refl 𝟎
  fg 𝟏 = refl 𝟏

  f-is-bijection : is-bijection f
  f-is-bijection = record { inverse = g ; η = gf ; ε = fg }

  _∔'_ : Type → Type → Type
  A ∔' B = (Σ b ꞉ Bool , P b)
    where
     P : Bool → Type
     P true = A
     P false = B

  f' : {A B : Type} → A ∔ B → A ∔' B
  f' (inl a) = true , a
  f' (inr b) = false , b

  g' : {A B : Type} → A ∔' B → A ∔ B
  g' (true , p) = inl p
  g' (false , p) = inr p

  l : {A B : Type} → (x : A ∔ B) → g' (f' x) ≡ x
  l (inl x) = refl (inl x)
  l (inr x) = refl (inr x)

  r : {A B : Type} → (x : A ∔' B) → f' (g' x) ≡ x
  r (true , p) = refl (true , p)
  r (false , p) = refl (false , p)

  binary-sum-is-bijection : {A B : Type} → A ∔ B ≅' A ∔' B
  binary-sum-is-bijection = record {f = f' ; g = g' ; l = l ; r = r}
```
And these are the only two isomorphisms (you could try to prove this in Agda as a rather advanced exercise). More advanced examples are in other files.

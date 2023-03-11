```agda
{-# OPTIONS --without-K --safe #-}

module binary-sum-iso-either where

open import prelude
open import isomorphisms
```

# The binary-sum type former `_∔_`

This is the same as (or, more precisely, [isomorphic](isomorphisms.lagda.md) to) the `Either` type defined earlier (you can try this as an exercise)

```agda
data Either (A B : Type) : Type where
 left  : A → Either A B
 right : B → Either A B

∔-iso-Either : {A B : Type} → A ∔ B ≅ Either A B
∔-iso-Either {A} {B} = record { bijection = f ; bijectivity = f-is-bijection }
 where
  f : A ∔ B → Either A B
  f (inl a) = left a
  f (inr b) = right b

  g : Either A B → A ∔ B
  g (left a) = inl a
  g (right b) = inr b

  gf : g ∘ f ∼ id
  gf (inl a) = refl (inl a)
  gf (inr b) = refl (inr b)

  fg : f ∘ g ∼ id
  fg (left a) = refl (left a)
  fg (right b) = refl (right b)

  f-is-bijection : is-bijection f
  f-is-bijection = record { inverse = g ; η = gf ; ε = fg }
```

```agda
{-# OPTIONS --without-K --safe #-}

module identity-type-exercises where

open import prelude
open import decidability
```

As an exercise, you may try to rewrite the following definitions to use `≡-nondep-elim` instead of pattern matching on `refl`:

```agda
trans' : {A : Type} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans' {A} {x} {y} {z} p = ?

sym' : {A : Type} {x y : A} → x ≡ y → y ≡ x
sym' p = {!!}

ap' : {A B : Type} (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
ap' f p = {!!}

ap₂' : {A B C : Type} (f : A → B → C) {x x' : A} {y y' : B}
     → x ≡ x' → y ≡ y' → f x y ≡ f x' y'
ap₂' f p1 p2 = {!!}

transport' : {X : Type} (A : X → Type)
           → {x y : X} → x ≡ y → A x → A y
transport' A p ax = {!!}
```

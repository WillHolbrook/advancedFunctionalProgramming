# Week 3 - Lab Sheet

```agda
{-# OPTIONS --without-K --safe #-}

module exercises.my-lab3v2 where
open import prelude hiding (𝟘-nondep-elim)
```

Before we proceed with the exercises, we introduce a some convenient notation
for multiple negations.

```agda
¬¬_ : Type → Type
¬¬ A = ¬ (¬ A)

¬¬¬ : Type → Type
¬¬¬ A = ¬ (¬¬ A)
```

## Part I: Propositional logic

### Section 1: Disjunction

#### Exercise 1.1

**Complete** the following proofs involving disjunctions.

```agda
private

 ∔-introduction-left  : {A B : Type} → A → A ∔ B
 ∔-introduction-left = inl

 ∔-introduction-right : {A B : Type} → B → A ∔ B
 ∔-introduction-right = inr
```

#### Exercise 1.2

**Complete** the proof about disjunctions.

```agda
 ∔-elimination : {A B X : Type} → (A → X) → (B → X) → (A ∔ B → X)
 ∔-elimination f g (inl a) = f a
 ∔-elimination f g (inr b) = g b
```

### Section 2: Conjunction

#### Exercise 2.1

**Complete** the following proofs involving conjunctions.

```agda
 ×-elimination-left : {A B : Type} → A × B → A
 ×-elimination-left = fst

 ×-elimination-right : {A B : Type} → A × B → B
 ×-elimination-right = snd
```

#### Exercise 2.2

**Prove** the following:

```agda
 ×-introduction : {A B : Type} → A → B → A × B
 ×-introduction a b = a , b

 ×-introduction' : {A B X : Type} → (X → A) → (X → B) → (X → A × B)
 ×-introduction' f g x = (f x) , (g x)
```

### Section 3: Implication

#### Exercise 3.1

**Complete** the following proofs involving implications.

```agda
 uncurry : {A B X : Type} → (A → B → X) → (A × B → X)
 uncurry f (a , b) = f a b

 curry : {A B X : Type} → (A × B → X) → (A → B → X)
 curry f a b = f (a , b)
```

You probably already know `curry` and `uncurry` from Haskell, but notice how we
can read them from a logical perspective: `uncurry` says that if `A` implies
that `B` implies `X`, then the conjunction of `A` and `B` implies `X`.

#### Exercise 3.2

**Prove** that implication is transitive.

```
 →-trans : {A B C : Type} → (A → B) → (B → C) → (A → C)
 →-trans f g a = g (f a)
```

Notice that the proof that implication is transitive is just function
composition.


### Section 4: Negation

The fact that falsity implies everything is known as the [_principle of
explosion_](https://en.wikipedia.org/wiki/Principle_of_explosion) or _ex falso
quodlibet_.

**Complete** the proof of the principle of explosion in Agda.

#### Exercise 4.1

```agda
 𝟘-nondep-elim : {A : Type} → 𝟘 → A
 𝟘-nondep-elim ()
```

#### Exercise 4.2

**Complete** the proof a proposition implies its own double negation.

```agda
 ¬¬-introduction : {A : Type} → A → ¬¬ A
 ¬¬-introduction a ¬a = ¬a a
```

#### Exercise 4.3

**Prove** that having three negations is the logically equivalent to having a
single negation.

```agda
 not-implies-not³ : {A : Type} → ¬ A → ¬¬¬ A
 not-implies-not³ ¬a ¬¬a = ¬¬a ¬a

 not³-implies-not : {A : Type} → ¬¬¬ A → ¬ A
 not³-implies-not ¬¬¬a a = ¬¬¬a (¬¬-introduction a)
```

#### Exercise 4.4

**Complete** the proof of contraposition.

```agda
 contraposition : {A B : Type} → (A → B) → ¬ B → ¬ A
 contraposition f ¬b a = ¬b (f a)
```

#### Exercise 4.5

Use `contraposition` to **complete** the following two proofs.

```agda
 ¬¬-functor : {A B : Type} → (A → B) → ¬¬ A → ¬¬ B
 ¬¬-functor f ¬¬a ¬b = ¬¬a (contraposition f ¬b)

 ¬¬-kleisli : {A B : Type} → (A → ¬¬ B) → ¬¬ A → ¬¬ B
 ¬¬-kleisli f ¬¬a = not³-implies-not (¬¬-functor f ¬¬a)
```

### Section 5: De Morgan Laws and logical laws

The De Morgan laws cannot be proved in Agda, though some of the implications
involved in the De Morgan laws _can_ be. The following exercises will involve
proving these (and some other similar laws) for Agda types.

#### Exercise 5.1

**Complete** the proofs.

```agda
 de-morgan₁ : {A B : Type} → ¬ (A ∔ B) → ¬ A × ¬ B
 de-morgan₁ ¬aorb = (λ a → ¬aorb (inl a)) , (λ b → ¬aorb (inr b))

 de-morgan₂ : {A B : Type} → ¬ A ∔ ¬ B → ¬ (A × B)
 de-morgan₂ (inl ¬a) (a , b) = ¬a a
 de-morgan₂ (inr ¬b) (a , b) = ¬b b
```

#### Exercise 5.2

**Complete** the proofs.

```agda
 ¬-and-+-exercise₁ : {A B : Type} → ¬ A ∔ B → A → B
 ¬-and-+-exercise₁ (inl ¬a) a = 𝟘-elim (¬a a)
 ¬-and-+-exercise₁ (inr b)  a = b

 ¬-and-+-exercise₂ : {A B : Type} → ¬ A ∔ B → ¬ (A × ¬ B)
 ¬-and-+-exercise₂ (inl ¬a) (a , ¬b) = ¬a a
 ¬-and-+-exercise₂ (inr b)  (a , ¬b) = ¬b b
```

#### Exercise 5.3

**Prove** the distributivity laws for `×` and `∔`.

```agda
 distributivity₁ : {A B C : Type} → (A × B) ∔ C → (A ∔ C) × (B ∔ C)
 distributivity₁ (inl (a , b)) = (inl a) , (inl b)
 distributivity₁ (inr c)       = (inr c) , (inr c)

 distributivity₂ : {A B C : Type} → (A ∔ B) × C → (A × C) ∔ (B × C)
 distributivity₂ (inl a , c) = inl (a , c)
 distributivity₂ (inr b , c) = inr (b , c)
```

## Part II: Logic with quantifiers

### Section 1: Sums

#### Exercise 1.1

**Complete** the following constructions.

```agda
 Σ-introduction : {A : Type} {B : (A → Type)} → (a : A) → B a → (Σ a ꞉ A , B a)
 Σ-introduction a ba = a , ba

 Σ-to-× : {A : Type} {B : (A → Type)} → ((a , _) : (Σ a ꞉ A , B a)) → A × B a
 Σ-to-× (a , ba) = a , ba
```

#### Exercise 1.2

**Complete** the following proof about sums over Booleans.

```agda
 Σ-on-Bool : {B : Bool → Type} → (Σ x ꞉ Bool , B x) → B true ∔ B false
 Σ-on-Bool (true , bt)  = inl bt
 Σ-on-Bool (false , bf) = inr bf
```

### Section 2: Products

#### Exercise 2.1

Complete the proof.

```agda
 Π-apply : {A : Type} {B : (A → Type)} → ((a : A) → B a) → (a : A) → B a
 Π-apply f a = f a
```

#### Exercise 2.2

**Prove**  the following.

```agda
 Π-→ : {A : Type} {B C : A → Type}
     → ((a : A) → B a → C a)
     → ((a : A) → B a) → ((a : A) → C a)
 Π-→ f g a = f a (g a)
```

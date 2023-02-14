# Week 3 - Lab Sheet

```agda
{-# OPTIONS --allow-unsolved-metas #-}
module exercises.my-lab3 where
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
 ∔-introduction-left a = inl a

 ∔-introduction-right : {A B : Type} → B → A ∔ B
 ∔-introduction-right b  = inr b
```

#### Exercise 1.2

**Complete** the proof about disjunctions.

```agda
 ∔-elimination : {A B X : Type} → (A → X) → (B → X) → (A ∔ B → X)
 ∔-elimination ap bp (inl a) = ap a
 ∔-elimination ap bp (inr b) = bp b
```

### Section 2: Conjunction

#### Exercise 2.1

**Complete** the following proofs involving conjunctions.

```agda
 ×-elimination-left : {A B : Type} → A × B → A
 ×-elimination-left (a , b) = a

 ×-elimination-right : {A B : Type} → A × B → B
 ×-elimination-right (a , b) = b
```

#### Exercise 2.2

**Prove** the following:

```agda
 ×-introduction : {A B : Type} → A → B → A × B
 ×-introduction a b = (a , b)

 ×-introduction' : {A B X : Type} → (X → A) → (X → B) → (X → A × B)
 ×-introduction' pa pb x = (pa x , pb x)
```

### Section 3: Implication

#### Exercise 3.1

**Complete** the following proofs involving implications.

```agda
 uncurry : {A B X : Type} → (A → B → X) → (A × B → X)
 uncurry abx (a , b) = abx a b

 curry : {A B X : Type} → (A × B → X) → (A → B → X)
 curry anbx a b = anbx (a , b)
```

You probably already know `curry` and `uncurry` from Haskell, but notice how we
can read them from a logical perspective: `uncurry` says that if `A` implies
that `B` implies `X`, then the conjunction of `A` and `B` implies `X`.

#### Exercise 3.2

**Prove** that implication is transitive.

```
 →-trans : {A B C : Type} → (A → B) → (B → C) → (A → C)
 →-trans ab bc a = bc (ab a)
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
 ¬¬-introduction a na = na a
```

#### Exercise 4.3

**Prove** that having three negations is the logically equivalent to having a
single negation.

```agda
 not-implies-not³ : {A : Type} → ¬ A → ¬¬¬ A
 not-implies-not³ na nna = nna na

 not³-implies-not : {A : Type} → ¬¬¬ A → ¬ A
 not³-implies-not nnna a = nnna (¬¬-introduction a)

 strip-2-¬ : {A : Type} → ¬¬¬ A → ¬ A
 strip-2-¬ nnna a = nnna (¬¬-introduction a)
```

#### Exercise 4.4

**Complete** the proof of contraposition.

```agda
 contraposition : {A B : Type} → (A → B) → ¬ B → ¬ A
 contraposition ab nb a = nb (ab a)
```

#### Exercise 4.5

Use `contraposition` to **complete** the following two proofs.

```agda
 ¬¬-functor : {A B : Type} → (A → B) → ¬¬ A → ¬¬ B
 ¬¬-functor ab = contraposition (contraposition ab)
-- ¬¬-functor ab nna nb = 𝟘-elim (nna (contraposition ab nb))

 flip : {A B C : Type} → (A → B → C) → B → (A → C)
 flip abc b a = abc a b

 ¬¬-kleisli : {A B : Type} → (A → ¬¬ B) → ¬¬ A → ¬¬ B
 ¬¬-kleisli annb = strip-2-¬ ∘ (contraposition (contraposition annb))
-- ¬¬-kleisli annb = strip-2-¬ ∘ ¬¬-functor annb
-- ¬¬-kleisli annb nna nb = 𝟘-elim ((nna (flip annb nb)))


```

### Section 5: De Morgan Laws and logical laws

The De Morgan laws cannot be proved in Agda, though some of the implications
involved in the De Morgan laws _can_ be. The following exercises will involve
proving these (and some other similar laws) for Agda types.

#### Exercise 5.1

**Complete** the proofs.

```agda
 de-morgan₁ : {A B : Type} → ¬ (A ∔ B) → ¬ A × ¬ B
 de-morgan₁ naorb = (λ a → naorb (inl a)) , λ b → naorb (inr b)

 de-morgan₂ : {A B : Type} → ¬ A ∔ ¬ B → ¬ (A × B)
 de-morgan₂ (inl na) (a , b) = na a
 de-morgan₂ (inr nb) (a , b) = nb b
```

#### Exercise 5.2

**Complete** the proofs.

```agda
 ¬-and-+-exercise₁ : {A B : Type} → ¬ A ∔ B → A → B
 ¬-and-+-exercise₁ (inl na) a = 𝟘-elim (na a)
 ¬-and-+-exercise₁ (inr b) a = b

 ¬-and-+-exercise₂ : {A B : Type} → ¬ A ∔ B → ¬ (A × ¬ B)
 ¬-and-+-exercise₂ (inl na) (a , nb) = 𝟘-elim (na a)
 ¬-and-+-exercise₂ (inr b) (a , nb) = nb b
```

#### Exercise 5.3

**Prove** the distributivity laws for `×` and `∔`.

```agda
 distributivity₁ : {A B C : Type} → (A × B) ∔ C → (A ∔ C) × (B ∔ C)
 distributivity₁ (inl (a , b)) = (inl a) , (inl b)
 distributivity₁ (inr c) = (inr c) , (inr c)

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
 Σ-on-Bool (true , bx) = inl bx
 Σ-on-Bool (false , bx) = inr bx
```

### Section 2: Products

#### Exercise 2.1

Complete the proof.

```agda
 Π-apply : {A : Type} {B : (A → Type)} → ((a : A) → B a) → (a : A) → B a
 Π-apply a→ba a = a→ba a
```

#### Exercise 2.2

**Prove**  the following.

```agda
 Π-→ : {A : Type} {B C : A → Type}
     → ((a : A) → B a → C a)
     → ((a : A) → B a) → ((a : A) → C a)
 Π-→ a→ba→ca a→ba a = a→ba→ca a (a→ba a)
```

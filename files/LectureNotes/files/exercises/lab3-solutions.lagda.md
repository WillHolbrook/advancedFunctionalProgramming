# Week 3 - Lab Sheet - Solutions

```agda
{-# OPTIONS --without-K --safe #-}

module exercises.lab3-solutions where
open import prelude hiding (π-nondep-elim)

Β¬Β¬_ : Type β Type
Β¬Β¬ A = Β¬ (Β¬ A)

Β¬Β¬Β¬ : Type β Type
Β¬Β¬Β¬ A = Β¬ (Β¬Β¬ A)

private
 β-introduction-left  : {A B : Type} β A β A β B
 β-introduction-left a = inl a

 β-introduction-right : {A B : Type} β B β A β B
 β-introduction-right b = inr b

 β-elimination : {A B X : Type} β (A β X) β (B β X) β (A β B β X)
 β-elimination p q (inl a) = p a
 β-elimination p q (inr b) = q b


 Γ-elimination-left : {A B : Type} β A Γ B β A
 Γ-elimination-left (a , b) = a

 Γ-elimination-right : {A B : Type} β A Γ B β B
 Γ-elimination-right (a , b) = b

 Γ-introduction : {A B : Type} β A β B β A Γ B
 Γ-introduction a b = (a , b)

 Γ-introduction' : {A B X : Type} β (X β A) β (X β B) β (X β A Γ B)
 Γ-introduction' p q x = (p x , q x)


 uncurry : {A B X : Type} β (A β B β X) β (A Γ B β X)
 uncurry p (a , b) = p a b

 curry : {A B X : Type} β (A Γ B β X) β (A β B β X)
 curry p a b = p (a , b)

 β-trans : {A B C : Type} β (A β B) β (B β C) β (A β C)
 β-trans p q = Ξ» a β q (p a)


 π-nondep-elim : {A : Type} β π β A
 π-nondep-elim = Ξ» ()

 Β¬Β¬-introduction : {A : Type} β A β Β¬Β¬ A
 Β¬Β¬-introduction a = Ξ» p β p a

 not-implies-notΒ³ : {A : Type} β Β¬ A β Β¬Β¬Β¬ A
 not-implies-notΒ³ p = Ξ» q β q p

 notΒ³-implies-not : {A : Type} β Β¬Β¬Β¬ A β Β¬ A
 notΒ³-implies-not p = Ξ» a β p (Ξ» q β q a)

 contraposition : {A B : Type} β (A β B) β Β¬ B β Β¬ A
 contraposition p q = Ξ» a β q (p a)

 Β¬Β¬-functor : {A B : Type} β (A β B) β Β¬Β¬ A β Β¬Β¬ B
 Β¬Β¬-functor p = contraposition (contraposition p)

 Β¬Β¬-kleisli : {A B : Type} β (A β Β¬Β¬ B) β Β¬Β¬ A β Β¬Β¬ B
 Β¬Β¬-kleisli p = contraposition (Ξ» q β Ξ» a β p a q)


 de-morganβ : {A B : Type} β Β¬ (A β B) β Β¬ A Γ Β¬ B
 de-morganβ {A} {B} p = Γ-introduction pβ pβ
  where
   pβ : Β¬ A
   pβ = p β β-introduction-left
   pβ : Β¬ B
   pβ = p β β-introduction-right

 de-morganβ : {A B : Type} β Β¬ A β Β¬ B β Β¬ (A Γ B)
 de-morganβ = β-elimination (β-trans Γ-elimination-left)
                            (β-trans Γ-elimination-right)

 Β¬-and-+-exerciseβ : {A B : Type} β Β¬ A β B β A β B
 Β¬-and-+-exerciseβ (inl p) a = π-nondep-elim (p a)
 Β¬-and-+-exerciseβ (inr q) _ = q

 Β¬-and-+-exerciseβ : {A B : Type} β Β¬ A β B β Β¬ (A Γ Β¬ B)
 Β¬-and-+-exerciseβ (inl p) = Ξ» { (a , _) β p a }
 Β¬-and-+-exerciseβ (inr q) = Ξ» { (a , r) β r q }

 distributivityβ : {A B C : Type} β (A Γ B) β C β (A β C) Γ (B β C)
 distributivityβ {A} {B} {C} = β-elimination qβ qβ
  where
   qβ : A Γ B β (A β C) Γ (B β C)
   qβ (a , b) = (inl a , inl b)
   qβ : C β A β C Γ B β C
   qβ c = (inr c , inr c)

 distributivityβ : {A B C : Type} β (A β B) Γ C β (A Γ C) β (B Γ C)
 distributivityβ (p , c) =
  β-elimination (Ξ» a β inl (a , c)) (Ξ» b β inr (b , c)) p


 Ξ£-introduction : {A : Type} {B : (A β Type)} β (a : A) β B a β (Ξ£ a κ A , B a)
 Ξ£-introduction a b = (a , b)

 Ξ£-to-Γ : {A : Type} {B : (A β Type)} β ((a , _) : (Ξ£ a κ A , B a)) β A Γ B a
 Ξ£-to-Γ (a , b) = (a , b)

 Ξ£-on-Bool : {B : Bool β Type} β (Ξ£ x κ Bool , B x) β B true β B false
 Ξ£-on-Bool (true  , b) = inl b
 Ξ£-on-Bool (false , b) = inr b


 Ξ -apply : {A : Type} {B : (A β Type)} β ((a : A) β B a) β (a : A) β B a
 Ξ -apply p a = p a

 Ξ -β : {A : Type} {B C : A β Type}
     β ((a : A) β B a β C a)
     β ((a : A) β B a) β ((a : A) β C a)
 Ξ -β p q = Ξ» a β p a (q a)

```

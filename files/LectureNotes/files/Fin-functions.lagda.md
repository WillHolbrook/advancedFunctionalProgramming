<!--
```agda
{-# OPTIONS --without-K --safe #-}

module Fin-functions where

open import prelude
```
-->

# Isomorphism of Fin n with a Basic MLTT type

```agda
Fin' : โ โ Type
Fin' 0       = ๐
Fin' (suc n) = ๐ โ Fin' n

zero' : {n : โ} โ Fin' (suc n)
zero' = inl โ

suc'  : {n : โ} โ Fin' n โ Fin' (suc n)
suc' fn = inr fn

open import Fin
open import isomorphisms

Fin-isomorphism : (n : โ) โ Fin n โ Fin' n
Fin-isomorphism n = record { bijection = f n ; bijectivity = f-is-bijection n }
 where
  f : (n : โ) โ Fin n โ Fin' n
  f (suc n) zero    = zero'
  f (suc n) (suc k) = suc' (f n k)
  -- f (suc n) zero = zero'
  -- f (suc n) (suc fn) = suc' IH
  --   where
  --     IH : Fin' n
  --     IH = f n fn

  g : (n : โ) โ Fin' n โ Fin n
  g (suc n) (inl โ) = zero
  g (suc n) (inr k) = suc (g n k)

  gf : (n : โ) โ g n โ f n โผ id
  gf (suc n) zero    = refl zero
  gf (suc n) (suc k) = {!!}
   where
    IH : g n (f n k) โก k
    IH = gf n k
    
    ฮณ = g (suc n) (f (suc n) (suc k)) โกโจ refl _ โฉ
        g (suc n) (suc' (f n k))      โกโจ refl _ โฉ
        suc (g n (f n k))             โกโจ ap suc IH โฉ
        suc k                         โ

  fg : (n : โ) โ f n โ g n โผ id
  fg (suc n) (inl โ) = refl (inl โ)
  fg (suc n) (inr k) = ฮณ
   where
    IH : f n (g n k) โก k
    IH = fg n k

    ฮณ = f (suc n) (g (suc n) (suc' k)) โกโจ refl _ โฉ
        f (suc n) (suc (g n k))        โกโจ refl _ โฉ
        suc' (f n (g n k))             โกโจ ap suc' IH โฉ
        suc' k                         โ

  f-is-bijection : (n : โ) โ is-bijection (f n)
  f-is-bijection n = record { inverse = g n ; ฮท = gf n ; ฮต = fg n}
```

**Exercise Done in exercises-fin.** Show that the type `Fin n` is isormorphic to the type `ฮฃ k : โ , k < n`.

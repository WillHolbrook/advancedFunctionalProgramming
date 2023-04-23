<!--
```agda
{-# OPTIONS --without-K --safe #-}
module my-regexp where

open import prelude
open import isomorphisms
open import List
open import List-functions
open import Maybe
open import decidability

open Maybe-Monad
```
-->

# Regular Expressions

This is based on the paper [Intrinsic Verification of a Regular Expression Matcher](https://dlicata.wescreates.wesleyan.edu/pubs/ktl16regexp/ktl16regexp.pdf).

We start by defining our basic regular expressions.  The type `A` here
will serve as the alphabet.  Because we will want to compare elements
of `A` for equality later on, we also assume that `A` has decidable
equality.


```agda
module Regexp (A : Type) (compare : has-decidable-equality A) where

  data RegExp : Type where
    ∅ : RegExp
    `_ : A → RegExp
    _·_ : RegExp → RegExp → RegExp
    _∪_ : RegExp → RegExp → RegExp
    _+ : RegExp → RegExp

```

```agda
  data _accepts_ : RegExp → List A → Type where

    acc-` : {!!}

    acc-∙ : {!!}

    acc-∪-inl : {!!}
    acc-∪-inr : {!!}

    acc-+-one : {!!}
    acc-+-many : {!!}

  String : Type
  String = List A

  Stack : Type
  Stack = List RegExp

  _stack-accepts_ : Stack → String → Type

  record MatchResult (ρ : RegExp) (ρs : List RegExp) (inp : List A) : Type where
    constructor ⟪_,_,_,_,_⟫
    inductive
    eta-equality
    field
      hd : {!!}
      tl : {!!}
      hd-acc : {!!}
      tl-acc : {!!}
      recons : {!!}

  open MatchResult

  _stack-accepts_ = {!!}

  match : (ρ : RegExp) (ρs : List RegExp) (inp : List A) → Maybe (MatchResult ρ ρs inp)
  match-stack : (ρs : List RegExp) (inp : List A) → Maybe (ρs stack-accepts inp)

  match = {!!}

  match-stack = {!!}


module Example where

  data Alph : Type where
    A : Alph
    B : Alph

  compare-Alph : has-decidable-equality Alph
  compare-Alph = {!!}

  open Regexp Alph compare-Alph

  AorB : RegExp
  AorB = {!!}

  example : AorB accepts (A :: A :: B :: [])
  example = {!!}
```

<!--
```agda
{-# OPTIONS --without-K --safe #-}

module curry-howard where

open import general-notation
```
-->
# Propositions as types and basic Martin-LΓΆf type theory

We now complete the proposition-as-types interpretation of logic.

| Logic           | English                    | Type theory   | Agda          | Handouts                                            | Alternative terminology               |
| ---             | ---                        | ---           | ---           | ---                                                 | ---                                   |
| β₯               | false                      | ββ            | π             | [empty type](empty-type.lagda.md)                   |                                       |
| β€               | true (*)                   | ββ            | π             | [unit type](unit-type.lagda.md)                     |                                       |
| A β§ B           | A and B                    | A Γ B         | A Γ B         | [binary product](binary-products.lagda.md) | cartesian product                        |
| A β¨ B           | A or B                     | A + B         | A β B         | [binary sum](binary-sums.lagda.md)                   | coproduct, <br> binary disjoint union      |
| A β B           | A implies B                | A β B         | A β B         | [function type](products.lagda.md)                   | non-dependent function type           |
| Β¬ A             | not A                      | A β ββ        | A β π         | [negation](negation.lagda.md)                       |                                       |
| β x : A, B x    | for all x:A, B x           | Ξ  x : A , B x | (x : A) β B x | [product](products.lagda.md)                         | dependent function type               |
| β x : A, B x    | there is x:A such that B x | Ξ£ x κ A , B x | Ξ£ x κ A , B x | [sum](sums.lagda.md)                                 | disjoint union, <br> dependent pair type   |
| x = y           | x equals y                 | Id x y        | x β‘ y         | [identity type](identity-type.lagda.md)             | equality type, <br> propositional equality |

## Remarks

 * (*) Not only the unit type π, but also any type with at least one element can be regarded as "true" in the propositions-as-types interpretation.

 * In Agda we can use any notation we like, of course, and people do use slightly different notatations for e.g. `π`, `π`, `+` and `Ξ£`.

 * We will refer to the above type theory together with the type `β` of natural numbers as *Basic Martin-LΓΆf Type Theory*.

 * As we will see, this type theory is very expressive and allows us to construct rather sophisticated types, including e.g. lists, vectors and trees.

 * All types in MLTT ([Martin-LΓΆf type theory](http://archive-pml.github.io/martin-lof/pdfs/Bibliopolis-Book-1984.pdf)) come with *introduction* and *elimination* principles.

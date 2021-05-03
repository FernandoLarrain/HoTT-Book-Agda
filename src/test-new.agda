{-# OPTIONS --without-K --exact-split #-}

module test-new where

-- Chapter 1

open import Ch1.3-Universes-and-families public
-- infix  1 _̇
open import Ch1.2-Function-types public
-- infixl 70 _∘_
open import Ch1.4-Dependent-function-types public
-- infixr -1 -Π
open import Ch1.6-Dependent-pair-types public
-- infixr 50 _,_
-- infixr -1 -Σ
open import Ch1.5-Product-types public
-- infixr 30 _×_
open import Ch1.7-Coproduct-types public
-- infixl 20 _+_
open import Ch1.8-The-type-of-booleans public
-- infix 0 Id
-- infix 0 _≡_
open import Ch1.9-The-natural-numbers public
open import Ch1.11-Propositions-as-types public
-- infix _⇔_ 10
open import Ch1.12-Identity-types public
-- infix 0 _≢_


-- Chapter 2

open import Ch2.1-Types-are-higher-groupoids public
-- infix 40 _⁻¹
-- infixl 30 _∙_
-- infixr 0 _≡⟨_⟩_
-- infix 1 _∎
-- infix 30 _∙ᵣ_
-- infix 30 _∙ₗ_
-- infixl 30 _✦_
-- infixl 30 _✧_
open import Ch2.2-Functions-are-functors public
open import Ch2.3-Type-families-are-fibrations public
-- infix 0 PathOver
open import Ch2.4-Homotopies-and-equivalences public
-- infix 0 _∼_
-- infixl 30 _·_
-- infixr 0 _∼⟨_⟩_
-- infix 1 _□
-- infix 30 _·ᵣ_
-- infix 30 _·ₗ_
-- infix 10 _≃_
-- infixl 30 _●_
-- infixr 0 _≃⟨_⟩_
-- infix 1 _■
open import Ch2.6-Cartesian-product-types public
open import Ch2.7-Σ-types public
open import Ch2.8-The-unit-type public
open import Ch2.9-Π-types-and-funext public
open import Ch2.10-Universes-and-univalence public
open import Ch2.11-Identity-type public
open import Ch2.12-Coproducts public
open import Ch2.13-Natural-numbers public
open import Ch2.14-Equality-of-structures public
open import Ch2.15-Universal-properties public
open import Ch2.Exercises public


-- Chapter 3

open import Ch3.1-Sets-and-n-types public
open import Ch3.2-Propositions-as-types public
open import Ch3.3-Mere-propositions public
open import Ch3.4-Classical-vs-intuitionistic-logic public
open import Ch3.5-Subsets-and-prop-resizing public
open import Ch3.6-The-logic-of-mere-props public
open import Ch3.7-Propositional-truncation public
-- infix 0 ∥_∥₋₁
-- infixl 20 _∨_
-- infixr -1 -∃
open import Ch3.9-The-pple-of-unique-choice public
open import Ch3.11-Contractibility public
open import Ch3.Exercises public


-- Chapter 4

open import Ch4.2-Half-adjoint-equivalences public
open import Ch4.3-Bi-invertible-maps public
open import Ch4.4-Contractible-fibers public
open import Ch4.5-On-the-definition-of-equivalences public
open import Ch4.6-Surjections-and-embeddings public
open import Ch4.7-Closure-properties-of-equivalences public
open import Ch4.8-The-object-classifier public
open import Ch4.9-Univalence-implies-funext public
open import Ch4.Exercises public
open import Ch4.1-Quasi-inverses public


-- Chapter 5

open import Ch5.1-Introduction-to-inductive-types public
open import Ch5.3-W-types public
open import Ch5.4-Inductive-types-are-initial-algebras public
open import Ch5.8-Id-types-and-id-systems public
open import Ch5.Exercises public

import Thesis.WildCats
open import Thesis.Z-Algebras public
open import Thesis.Identity-types public
open import Thesis.Hinitial-Z-Algebras public
open import Thesis.Inductive-Z-Algebras public
open import Thesis.Equivalence-preservation public
open import Thesis.ZAlg-is-Cofiltered public
open import Thesis.Ind-iff-hinit public
open import Thesis.Slice public


-- Chapter 6: Safe

open import Ch6.4-Circles-and-spheres-safe public
open import Ch6.5-Suspensions-safe public
open import Ch6.9-Truncations public
open import Ch6.11-Algebra public
-- infixr 30 _++_
open import Ch6.Exercises public

open import Rewrite public

open import Ch6.2-Induction-pples-and-dependent-paths public
open import Ch6.3-The-interval public
open import Ch6.4-Circles-and-spheres public
open import Ch6.5-Suspensions public
open import Ch6.8-Pushouts public
open import Ch6.10-Quotients public

open import Thesis.Z-as-HIT public


-- Chapter 7: Safe

open import Ch7.1-Definition-of-n-types public
open import Ch7.2-UIP-and-Hedberg's-theorem-safe public
open import Ch7.3-Truncations-safe public
open import Ch7.5-Connectedness public
open import Ch7.6-Orthogonal-factorization public

open import Ch7.2-UIP-and-Hedberg's-theorem public
open import Ch7.3-Truncations public

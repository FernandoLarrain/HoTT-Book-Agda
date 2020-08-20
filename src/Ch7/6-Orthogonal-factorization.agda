{-# OPTIONS --without-K --exact-split --safe #-}

open import Ch1.Type-theory
open import Ch2.Homotopy-type-theory
open import Ch3.Sets-and-logic
open import Ch4.Equivalences
open import Ch6.9-Truncations
open import Ch7.1-Definition-of-n-types
open import Ch7.3-Truncations-safe
open import Ch7.5-Connectedness

module Ch7.6-Orthogonal-factorization ⦃ tc : Truncations ⦄ where


-- Definition 7.6.1 (n-truncated function).

trunc : Tlevel → {A : 𝓤 ̇} {B : 𝓥 ̇} → (A → B) → 𝓤 ⊔ 𝓥 ̇
trunc n {A} {B} f = (b : B) → is n type (fib f b)

trunc-is-Prop : ⦃ fe : FunExt ⦄ (n : Tlevel) {A : 𝓤 ̇} {B : 𝓥 ̇} (f : A → B) → isProp (trunc n f )
trunc-is-Prop n f = Π-preserves-Props _ (λ b → Tlevel-is-predicate _ _)


-- Lemma 7.6.2 (Recursive definition of n-truncated maps).


-- Definition 7.6.3 (n-image of a function)

im : Tlevel → {A : 𝓤 ̇} {B : 𝓥 ̇} → (A → B) → 𝓤 ⊔ 𝓥 ̇
im n {A} {B} f = Σ b ꞉ B , (∥ fib f b ∥ n)




 

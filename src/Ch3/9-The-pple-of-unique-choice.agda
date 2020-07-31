{-# OPTIONS --without-K --exact-split --safe #-}

open import Ch1.Type-theory
open import Ch2.Homotopy-type-theory
open import Ch3.3-Mere-propositions
open import Ch3.7-Propositional-truncation

module Ch3.9-The-pple-of-unique-choice where


module unique-choice (pt : propositional-truncations-exist) where

  open basic-truncation-development pt


  -- Lemma 3.9.1 (Truncating a proposition does nothing).

  trunc-of-Prop-is-Prop : (P : 𝓤 ̇ ) → isProp P → P ≃ ∥ P ∥
  trunc-of-Prop-is-Prop P i = ⇔-to-≃ i ∥∥-is-Prop (∣_∣ , ∥∥-recursion i (𝑖𝑑 P))


  -- Corollary 3.9.2 (The principle of unique choice).

  pple-of-unique-choice : {A : 𝓤 ̇ } {P : A → 𝓥 ̇ } → ((x : A) → isProp (P x)) → ((x : A) → ∥ P x ∥) → (x : A) → P x
  pple-of-unique-choice {A = A} {P} i f x = ∥∥-recursion (i x) (𝑖𝑑 (P x)) (f x)


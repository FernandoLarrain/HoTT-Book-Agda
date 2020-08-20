{-# OPTIONS --without-K --exact-split --safe #-}

open import Ch1.Type-theory
open import Ch2.Homotopy-type-theory
open import Ch3.3-Mere-propositions
open import Ch3.7-Propositional-truncation

module Ch3.9-The-pple-of-unique-choice where


module _ ⦃ pt : PropTrunc ⦄ where

  -- Lemma 3.9.1 (Truncating a proposition does nothing).

  trunc-of-Prop-is-Prop : (P : 𝓤 ̇) → isProp P → P ≃ ∥ P ∥₋₁
  trunc-of-Prop-is-Prop P i = ⇔-to-≃ i ∥∥₋₁-is-Prop (∣_∣₋₁ , ∥∥₋₁-recursion i (𝑖𝑑 P))


  -- Corollary 3.9.2 (The principle of unique choice).

  pple-of-unique-choice : {A : 𝓤 ̇} {P : A → 𝓥 ̇} → ((x : A) → isProp (P x)) → ((x : A) → ∥ P x ∥₋₁) → (x : A) → P x
  pple-of-unique-choice {𝓤} {𝓥} {A} {P} i f x = ∥∥₋₁-recursion (i x) (𝑖𝑑 (P x)) (f x)


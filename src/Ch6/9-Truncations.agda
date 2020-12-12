{-# OPTIONS --without-K --exact-split #-}

open import Ch1.Type-theory
open import Ch2.Homotopy-type-theory
open import Ch3.Sets-and-logic
open import Ch4.Equivalences

module Ch6.9-Truncations where

-- Definition of set truncations.

{- Note: Rather than proving Lemma 6.9.1, we assume it as part of the definition of set truncation. We derive truncations from HITs in Ch7.3. -}
 
record SetTrunc : 𝓤ω where
  field
    ∥_∥₀ : {𝓤 : Universe} → 𝓤 ̇ → 𝓤 ̇ 
    ∣_∣₀ : {𝓤 : Universe} {A : 𝓤 ̇} → A → ∥ A ∥₀
    ∥∥₀-is-Set : {𝓤 : Universe} {A : 𝓤 ̇} → isSet ∥ A ∥₀
    ∥∥₀-induction : {𝓤 𝓥 : Universe} {A : 𝓤 ̇} {P : ∥ A ∥₀ → 𝓥 ̇} → ((x : ∥ A ∥₀) → isSet (P x)) → ((a : A) → P ∣ a ∣₀) → (x : ∥ A ∥₀) → P x
    ∣∣₀-prop-β : {𝓤 𝓥 : Universe} {A : 𝓤 ̇} {P : ∥ A ∥₀ → 𝓥 ̇} (i : (x : ∥ A ∥₀) → isSet (P x)) (g : (a : A) → P ∣ a ∣₀) (a : A) → ∥∥₀-induction i g ∣ a ∣₀ ≡ g a

  infix 0 ∥_∥₀

open SetTrunc ⦃ ... ⦄ public

module _ ⦃ st : SetTrunc ⦄ where


  -- Recursion principle for set truncation

  ∥∥₀-recursion : {A : 𝓤 ̇} {B : 𝓥 ̇} → isSet B → (A → B) → ∥ A ∥₀ → B
  ∥∥₀-recursion i g = ∥∥₀-induction (λ - → i) g


  -- Propositional computation rule for ∥∥₀-recursion

  ∣∣₀-prop-β' : {A : 𝓤 ̇} {B : 𝓥 ̇} (i : isSet B) (g : A → B) (a : A) → ∥∥₀-recursion i g ∣ a ∣₀ ≡ g a
  ∣∣₀-prop-β' i g = ∣∣₀-prop-β (λ - → i) g


  -- Uniqueness principle for set truncation

  ∥∥₀-uniqueness-pple : {A : 𝓤 ̇} {B : 𝓥 ̇} → isSet B → (f g : ∥ A ∥₀ → B) → f ∘ ∣_∣₀ ∼ g ∘ ∣_∣₀ → f ∼ g
  ∥∥₀-uniqueness-pple i f g agreement = ∥∥₀-induction (λ x → isProp-to-isSet (i _ _)) agreement

  -- Lemma 6.9.2 (UMP of set truncation).

  module ∥∥₀-UMP (A : 𝓤 ̇) {B : 𝓥 ̇} (i : isSet B) where

    ϕ : (∥ A ∥₀ → B) → A → B
    ϕ = _∘ ∣_∣₀

    ψ : (A → B) → ∥ A ∥₀ → B
    ψ g = ∥∥₀-recursion i g

    β : ϕ ∘ ψ ∼ id
    β g = funext (∣∣₀-prop-β' i g)

    η : ψ ∘ ϕ ∼ id
    η f = funext (∥∥₀-uniqueness-pple i (ψ (ϕ f)) f (∣∣₀-prop-β' i (ϕ f)))

    equiv : (∥ A ∥₀ → B) ≃ (A → B)
    equiv = ϕ , qinv-to-isequiv (ψ , β , η)


  -- Lemma 6.9.3 (Set pushout): see Ch6.8-Pushouts.

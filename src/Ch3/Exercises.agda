{-# OPTIONS --without-K --exact-split --safe #-}

open import Ch1.Type-theory
open import Ch2.Homotopy-type-theory
open import Ch3.3-Mere-propositions
open import Ch3.6-The-logic-of-mere-props
open import Ch3.11-Contractibility

module Ch3.Exercises where


-- Exercise 3.5

isProp-≃-inhabited→isContr : ⦃ fe : FunExt ⦄ (A : 𝓤 ̇) → isProp A ≃ (A → isContr A)
isProp-≃-inhabited→isContr A = ⇔-to-≃ (isProp-is-Prop _) (Π-preserves-Props _ (λ a → isContr-is-Prop _)) (sufficiency , necessity)
  where
  sufficiency : isProp A → A → isContr A
  sufficiency f a = pr₂ (isContr-iff-is-inhabited-Prop A) (a , f)
  necessity : (A → isContr A) → isProp A
  necessity g = λ x y → pr₂ (g x) x ⁻¹ ∙ pr₂ (g x) y
    

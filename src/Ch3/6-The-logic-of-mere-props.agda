{-# OPTIONS --without-K --exact-split --safe #-}

open import Ch1.Type-theory
open import Ch2.Homotopy-type-theory
open import Ch3.3-Mere-propositions

module Ch3.6-The-logic-of-mere-props where

-- Example 3.6.1. Props are closed under conjunction

×-preserves-Props : (A : 𝓤 ̇) (B : 𝓥 ̇) → isProp A → isProp B → isProp (A × B)
×-preserves-Props A B f g (a , b) (c , d) = pair-≡ ((f a c) , (g b d))


-- Example 3.6.2. Props are closed under universal quantification, implication and negation

module _ ⦃ fe : FunExt ⦄ where

  Π-preserves-Props : {A : 𝓤 ̇} (B : A → 𝓥 ̇) → ((x : A) → isProp (B x)) → isProp (Π B)
  Π-preserves-Props B ϕ f g = funext (λ x → ϕ x (f x) (g x))

  →-preserves-Props : (A : 𝓤 ̇) (B : 𝓥 ̇) → isProp B → isProp (A → B)
  →-preserves-Props A B i = Π-preserves-Props (λ a → B) (λ a → i)

  ¬-preserves-Props : (A : 𝓤 ̇) → isProp A → isProp (¬ A)
  ¬-preserves-Props A i = →-preserves-Props A 𝟘 𝟘-is-Prop

  biimplication-preserves-Props : (A : 𝓤 ̇) (B : 𝓥 ̇) → isProp A → isProp B → isProp ((A → B) × (B → A))
  biimplication-preserves-Props A B A-is-Prop B-is-Prop = ×-preserves-Props _ _ (→-preserves-Props _ _ B-is-Prop) (→-preserves-Props _ _ A-is-Prop)

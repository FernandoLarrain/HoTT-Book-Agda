{-# OPTIONS --without-K --exact-split #-}

open import Ch1.Type-theory
open import Ch2.Homotopy-type-theory
open import Ch3.1-Sets-and-n-types
open import Ch3.3-Mere-propositions
open import Ch3.6-The-logic-of-mere-props
open import Ch3.11-Contractibility

module Ch3.Exercises where


-- Exercise 3.1

≃-preserves-Props : {A : 𝓤 ̇} {B : 𝓥 ̇} → A ≃ B → isProp A → isProp B
≃-preserves-Props {𝓤} {𝓥} {A} {B} e A-is-Prop = pr₂ Prop-iff-Contr-≡ (λ x y → ≃-preserves-Contr (≃-sym (ap (inv e) , (ap-of-equiv-is-equiv (pr₂ (≃-sym e)) x y))) (pr₁ Prop-iff-Contr-≡ A-is-Prop _ _))

≃-preserves-Sets : {A : 𝓤 ̇} {B : 𝓥 ̇} → A ≃ B → isSet A → isSet B
≃-preserves-Sets {𝓤} {𝓥} {A} {B} e A-is-Set x y = ≃-preserves-Props (≃-sym (ap (inv e) , ap-of-equiv-is-equiv (pr₂ (≃-sym e)) x y)) (A-is-Set _ _)


-- Exercise 3.3

Σ-preserves-Props : {A : 𝓤 ̇} {B : A → 𝓥 ̇} → isProp A → ((x : A) → isProp (B x)) → isProp (Σ B)
Σ-preserves-Props A-is-Prop B-is-Prop-family = pr₂ Prop-iff-Contr-≡ (λ w w' → ≃-preserves-Contr (≃-sym Σ-≡-≃) (Σ-preserves-Contr (pr₁ Prop-iff-Contr-≡ A-is-Prop _ _) λ p → pr₁ Prop-iff-Contr-≡ (B-is-Prop-family _) _ _))

{- For Σ-preserves-Sets see Example 3.1.5. -}


-- Exercise 3.5

isProp-≃-inhabited-to-isContr : ⦃ fe : FunExt ⦄ (A : 𝓤 ̇) → isProp A ≃ (A → isContr A)
isProp-≃-inhabited-to-isContr A = ⇔-to-≃ (isProp-is-Prop _) (Π-preserves-Props _ (λ a → isContr-is-Prop _)) (sufficiency , necessity)
  where
  sufficiency : isProp A → A → isContr A
  sufficiency = swap inhabited-Prop-to-isContr
  necessity : (A → isContr A) → isProp A
  necessity g = λ x y → pr₂ (g x) x ⁻¹ ∙ pr₂ (g x) y


-- Points of a type

module pts-of-type ⦃ fe : FunExt ⦄ (A : 𝓤 ̇) {B : 𝓥 ̇} (c : isContr B) where

  b = pr₁ c
  contraction = pr₂ c

  ϕ : A → B → A
  ϕ = singleton-ind (b , contraction) (λ - → A)

  ψ : (B → A) → A
  ψ f = f b

  α : ϕ ∘ ψ ∼ id
  α f = funext (singleton-ind c (λ b → ϕ (ψ f) b ≡ f b) (center-prop-β c (λ - → A) (f b)))

  β : ψ ∘ ϕ ∼ id
  β a = ap (λ - → transport (λ a → A) - a) (B-is-Set _ _ (contraction b) (refl _))  where
    B-is-Set : isSet B
    B-is-Set = isProp-to-isSet (isContr-to-isProp c)  
  
  equiv : A ≃ (B → A)
  equiv =  ϕ , qinv-to-isequiv (ψ , α , β)

pts-of-type-𝟙 : ⦃ fe : FunExt ⦄ {A : 𝓤 ̇} → A ≃ (𝟙 → A)
pts-of-type-𝟙 {𝓤} {A} = (𝟙-recursion A) , (qinv-to-isequiv ((λ f → f ⋆) , ((λ f → funext (𝟙-induction _ (refl _))) , hrefl _))) 

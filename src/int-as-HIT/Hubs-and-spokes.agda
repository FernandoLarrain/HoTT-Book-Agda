{-# OPTIONS --without-K --exact-split --rewriting #-}

open import Ch1.Type-theory
open import Ch2.Homotopy-type-theory
open import Ch3.Sets-and-logic
open import Ch4.Equivalences
open import Rewrite
open import Ch6.2-Induction-pples-and-dependent-paths
open import Ch6.4-Circles-and-spheres
open import Ch6.5-Suspensions

module int-as-HIT.Hubs-and-spokes where

Eqv : (𝓤 : Universe) → 𝓤 ⁺ ̇
Eqv 𝓤 = Σ A₁ ꞉ (𝓤 ̇) , Σ A₂ ꞉ (𝓤 ̇) ,
         Σ s ꞉ (A₁ → A₂) ,
         Σ p ꞉ (A₂ → A₁) ,
         Σ σ ꞉ (p ∘ s ∼ id) ,
         Σ ρ ꞉ (s ∘ p ∼ id) ,
         Σ h ꞉ (A₁ → A₂) ,
         ((a₁ : A₁) (x : 𝕊¹) → 𝕊¹-rec (s a₁) (ap s (σ a₁) ⁻¹ ∙ ρ (s a₁)) x ≡ h a₁)


module EqvPreservation {A₁ A₂ : 𝓤 ̇} {B₁ B₂ : 𝓥 ̇} (f₁ : A₁ → B₁) (f₂ : A₂ → B₂) where

  module maps where

  s-pres : (A₁ → A₂) → (B₁ → B₂) → 𝓤 ⊔ 𝓥 ̇
  s-pres s s' = f₂ ∘ s ∼ s' ∘ f₁

  p-pres : (A₂ → A₁) → (B₂ → B₁) → 𝓤 ⊔ 𝓥 ̇
  p-pres p p' = f₁ ∘ p ∼ p' ∘ f₂

  h-pres : (A₁ → A₂) → (B₁ → B₂) → 𝓤 ⊔ 𝓥 ̇
  h-pres h h' = f₂ ∘ h ∼ h' ∘ f₁ 

  module htpies (s h : A₁ → A₂) (p : A₂ → A₁) (s' h' : B₁ → B₂) (p' : B₂ → B₁) (α : s-pres s s') (β : p-pres p p') (θ : h-pres h h') where

    aux-γ : f₁ ∘ p ∘ s ∼ p' ∘ s' ∘ f₁
    aux-γ a₁ = β (s a₁) ∙ ap p' (α a₁)

    σ-pres : (p ∘ s ∼ id) → (p' ∘ s' ∼ id) → 𝓤 ⊔ 𝓥 ̇
    σ-pres σ σ' = (a₁ : A₁) → ap f₁ (σ a₁) ≡ aux-γ a₁ ∙ σ' (f₁ a₁)

    aux-δ : f₂ ∘ s ∘ p ∼ s' ∘ p' ∘ f₂
    aux-δ a₂ = α (p a₂) ∙ ap s' (β a₂)

    ρ-pres : (s ∘ p ∼ id) → (s' ∘ p' ∼ id) → 𝓤 ⊔ 𝓥 ̇
    ρ-pres ρ ρ' = (a₂ : A₂) → ap f₂ (ρ a₂) ≡ aux-δ a₂ ∙ ρ' (f₂ a₂)

    module _ (σ : p ∘ s ∼ id) (ρ : s ∘ p ∼ id) (σ' : p' ∘ s' ∼ id) (ρ' : s' ∘ p' ∼ id) (γ : σ-pres σ σ') (δ : ρ-pres ρ ρ') where
    
      aux-ε : (a₁ : A₁) (x : 𝕊¹) → f₂ (𝕊¹-rec (s a₁) (ap s (σ a₁) ⁻¹ ∙ ρ (s a₁)) x) ≡ 𝕊¹-rec (s' (f₁ a₁)) (ap s' (σ' (f₁ a₁)) ⁻¹ ∙ ρ' (s' (f₁ a₁))) x
      aux-ε a₁ = 𝕊¹-ind
        (λ x → f₂ (𝕊¹-rec (s a₁) (ap s (σ a₁) ⁻¹ ∙ ρ (s a₁)) x) ≡ 𝕊¹-rec (s' (f₁ a₁)) (ap s' (σ' (f₁ a₁)) ⁻¹ ∙ ρ' (s' (f₁ a₁))) x)
        (α a₁)
        (transport-funval-≡ (f₂ ∘ 𝕊¹-rec (s a₁) (ap s (σ a₁) ⁻¹ ∙ ρ (s a₁))) (𝕊¹-rec (s' (f₁ a₁)) (ap s' (σ' (f₁ a₁)) ⁻¹ ∙ ρ' (s' (f₁ a₁)))) loop₁ (α a₁) ∙ {!!})
        where
        i : ap (f₂ ∘ 𝕊¹-rec (s a₁) (ap s (σ a₁) ⁻¹ ∙ ρ (s a₁))) loop₁ ≡ ap f₂ (ap s (σ a₁) ⁻¹) ∙ ap f₂ (ρ (s a₁))
        i = ap-∘ _ f₂ _ ⁻¹ ∙ ap (ap f₂) (loop₁-β' (s a₁) (ap s (σ a₁) ⁻¹ ∙ ρ (s a₁))) ∙ ap-∙ _ _ _

        -- The path looks doable, but it will be quite complicated. Is it worth doing? How will we prove the uniqueness pple for homomorphisms?

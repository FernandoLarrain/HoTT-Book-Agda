{-# OPTIONS --without-K --exact-split --safe #-}

open import Ch1.Type-theory
open import Ch2.Homotopy-type-theory
open import Ch3.Sets-and-logic
open import Ch4.Equivalences
open import Ch5.8-Id-types-and-id-systems
open import Ch7.1-Definition-of-n-types

module int-as-HIT.Z-as-1-HIT where

-- 1-truncated ℤ-algebras and their homomorphisms


is-hom : {A₁ A₂ : 𝓤 ̇} (e : A₁ ≃ A₂) {B₁ B₂ : 𝓥 ̇} (e' : B₁ ≃ B₂) → (A₁ → B₁) → (A₂ → B₂) → 𝓤 ⊔ 𝓥 ̇
is-hom {𝓤} {𝓥} {A₁} {A₂} (s , p , σ , ρ , τ) (s' , p' , σ' , ρ' , τ') f₁ f₂ =
  Σ α ꞉ f₂ ∘ s ∼ s' ∘ f₁ ,
  Σ β ꞉ f₁ ∘ p ∼ p' ∘ f₂ ,
    (
    ((a₁ : A₁) → ap f₁ (σ a₁) ≡ β (s a₁) ∙ ap p' (α a₁) ∙ σ' (f₁ a₁)) ×
    ((a₂ : A₂) → ap f₂ (ρ a₂) ≡ α (p a₂) ∙ ap s' (β a₂) ∙ ρ' (f₂ a₂))
    ) 
  

abstract

  simple-homs-refl : ⦃ fe : FunExt ⦄ (A : 𝓤 ̇) (B : 𝓥 ̇) (j : is-⟨1⟩-type B) →  (f₁ f₂ : A → B) → is-hom (≃-refl A) (≃-refl B) f₁ f₂ ≃ (f₂ ∼ f₁)
  simple-homs-refl A B j = λ f₁ f₂ → ϕ f₂ f₁ , qinv-to-isequiv (ψ f₂ f₁ , ϕ∘ψ f₂ f₁ , ψ∘ϕ f₂ f₁) where
    ϕ : (f₂ f₁ : A → B) → is-hom (≃-refl A) (≃-refl B) f₁ f₂ → (f₂ ∼ f₁)
    ϕ f₂ f₁ = pr₁
    ψ : (f₂ f₁ : A → B) → f₂ ∼ f₁ → is-hom (≃-refl A) (≃-refl B) f₁ f₂
    ψ = 𝕁-∼ (λ f₂ f₁ α → is-hom (≃-refl A) (≃-refl B) f₁ f₂) (λ f → hrefl f , hrefl f , hrefl (hrefl f) , hrefl (hrefl f))
    ϕ∘ψ : (f₂ f₁ : A → B) → ϕ f₂ f₁ ∘ ψ f₂ f₁ ∼ id
    ϕ∘ψ = 𝕁-∼ (λ f₂ f₁ α → ϕ f₂ f₁ (ψ f₂ f₁ α) ≡ α) (λ f → ϕ f f (ψ f f (hrefl f)) ≡⟨  ap (ϕ f f) (𝕁-∼-β (λ f₂ f₁ α → is-hom (≃-refl A) (≃-refl B) f₁ f₂) (λ f → hrefl f , hrefl f , hrefl (hrefl f) , hrefl (hrefl f)) f) ⟩ ϕ f f (hrefl f , hrefl f , hrefl (hrefl f) , hrefl (hrefl f)) ≡⟨ refl _ ⟩ hrefl f ∎)
    ψ∘ϕ : (f₂ f₁ : A → B) → ψ f₂ f₁ ∘ ϕ f₂ f₁ ∼ id
    ψ∘ϕ f₂ f₁ = Σ-induction (𝕁-∼ (λ f₂ f₁ α → (w : _) → ψ f₂ f₁ (ϕ f₂ f₁ (α , w)) ≡ (α , w)) (λ f → Σ-induction λ β → Σ-induction λ γ δ →  𝕁-∼-β (λ f₂ f₁ α → is-hom (≃-refl A) (≃-refl B) f₁ f₂) (λ f → hrefl f , hrefl f , hrefl (hrefl f) , hrefl (hrefl f)) f ∙ dpair-≡ (refl (hrefl f) , dpair-≡ (funext (λ x → δ x ∙ ru _ ⁻¹ ∙ lu _ ⁻¹ ∙ ap-id (β x)) , dpair-≡ (funext (λ x → j _ _ _ _ _ _) , funext (λ x → j _ _ _ _ _ _))))) f₂ f₁)


  simple-homs : ⦃ fe : FunExt ⦄ ⦃ univ : Univalence ⦄ (A₁ A₂ : 𝓤 ̇) (e : A₁ ≃ A₂) (B₁ B₂ : 𝓥 ̇) (e' : B₁ ≃ B₂) → is-⟨1⟩-type B₁ → (f₁ : A₁ → B₁) (f₂ : A₂ → B₂) → is-hom e e' f₁ f₂ ≃ (f₂ ∘ pr₁ e ∼ pr₁ e' ∘ f₁)
  simple-homs {𝓤} {𝓥} = 𝕁-≃ _ λ A → 𝕁-≃ _ (λ B j → simple-homs-refl A B j)









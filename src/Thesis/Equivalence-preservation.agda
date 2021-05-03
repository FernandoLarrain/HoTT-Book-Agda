{-# OPTIONS --without-K --exact-split --safe #-}

open import Ch1.Type-theory
open import Ch2.Homotopy-type-theory
open import Ch3.Sets-and-logic
open import Ch4.Equivalences
open import Ch5.8-Id-types-and-id-systems

module Thesis.Equivalence-preservation where 


-- I. Preservation of Equivalences

module Preservation-of-Equivalences (A₁ A₂ : 𝓤 ̇) (e : A₁ ≃ A₂) (B₁ B₂ : 𝓥 ̇) (e' : B₁ ≃ B₂) (f₁ : A₁ → B₁) (f₂ : A₂ → B₂) where

  s = pr₁ e
  i = pr₂ e
  p = ishae₁ i
  σ = ishae₂ i
  ρ = ishae₃ i
  τ = ishae₄ i

  s' = pr₁ e'
  i' = pr₂ e'
  p' = ishae₁ i'
  σ' = ishae₂ i'
  ρ' = ishae₃ i'
  τ' = ishae₄ i'

  s-pres : 𝓤 ⊔ 𝓥 ̇
  s-pres = f₂ ∘ s ∼ s' ∘ f₁

  p-pres : 𝓤 ⊔ 𝓥 ̇
  p-pres = f₁ ∘ p ∼ p' ∘ f₂

  module _ (f-s : s-pres) (f-p : p-pres) where

    f-σ-top : f₁ ∘ p ∘ s ∼ p' ∘ s' ∘ f₁
    f-σ-top a₁ = f-p (s a₁) ∙ ap p' (f-s a₁)

    σ-pres : 𝓤 ⊔ 𝓥 ̇
    σ-pres = (a₁ : A₁) → ap f₁ (σ a₁) ≡ f-σ-top a₁ ∙ σ' (f₁ a₁)

    f-ρ-top : f₂ ∘ s ∘ p ∼ s' ∘ p' ∘ f₂
    f-ρ-top a₂ = f-s (p a₂) ∙ ap s' (f-p a₂)

    ρ-pres : 𝓤 ⊔ 𝓥 ̇
    ρ-pres = (a₂ : A₂) → ap f₂ (ρ a₂) ≡ f-ρ-top a₂ ∙ ρ' (f₂ a₂)

    f-τ-top : f₂ ∘ s ∘ p ∘ s ∼ s' ∘ p' ∘ s' ∘ f₁
    f-τ-top a₁ = f-ρ-top (s a₁) ∙ ap s' (ap p' (f-s a₁))

    module _ (f-σ : σ-pres) (f-ρ : ρ-pres) where

      front : (a₁ : A₁) → ap f₂ (ap s (σ a₁)) ∙ f-s a₁ ≡ f-τ-top a₁ ∙ ap s' (σ' (f₁ a₁))
      front a₁ = (ap-∘ s f₂ (σ a₁) ∙ᵣ f-s a₁) ∙ hnat f-s (σ a₁) ⁻¹ ∙ (f-s (p (s a₁)) ∙ₗ (ap-∘ f₁ s' (σ a₁) ⁻¹ ∙ ap (ap s') (f-σ a₁) ∙ ap-∙ s' _ _)) ∙ ∙-assoc _ _ _ ∙ (((f-s (p (s a₁)) ∙ₗ ap-∙ s' _ _) ∙ ∙-assoc _ _ _) ∙ᵣ ap s' (σ' (f₁ a₁)))

      back : (a₁ : A₁) → ap f₂ (ρ (s a₁)) ∙ f-s a₁ ≡ f-τ-top a₁ ∙ ρ' (s' (f₁ a₁))
      back a₁ = (f-ρ (s a₁) ✦ ap-id (f-s a₁) ⁻¹) ∙ ∙-assoc _ _ _ ⁻¹ ∙ (f-ρ-top (s a₁) ∙ₗ (hnat ρ' (f-s a₁) ∙ (ap-∘ p' s' (f-s a₁) ⁻¹ ∙ᵣ ρ' (s' (f₁ a₁))))) ∙ ∙-assoc _ _ _

      τ-pres : 𝓤 ⊔ 𝓥 ̇
      τ-pres = (a₁ : A₁) → (ap (ap f₂) (τ a₁) ∙ᵣ f-s a₁) ∙ back a₁ ≡ front a₁ ∙ (f-τ-top a₁ ∙ₗ τ' (f₁ a₁))

  ishae-pres : (f-s : s-pres) → 𝓤 ⊔ 𝓥 ̇
  ishae-pres f-s = Σ f-p ꞉ p-pres , Σ f-σ ꞉ σ-pres f-s f-p , Σ f-ρ ꞉ ρ-pres f-s f-p , τ-pres f-s f-p f-σ f-ρ

  hae-pres : 𝓤 ⊔ 𝓥 ̇
  hae-pres = Σ f-s ꞉ s-pres , ishae-pres f-s


-- II. Equivalence Preservation is Function Preservation

module _ (univ : Univalence) where

  open Full-Univalence univ

  module _ (A : 𝓤 ̇) (B : 𝓥 ̇) (f : A → B) where

    open Preservation-of-Equivalences A A (≃-refl A) B B (≃-refl B) f f 

    ishae-pres-is-Contr' : isContr (ishae-pres (hrefl _))
    ishae-pres-is-Contr' = ≃-preserves-Contr (≃-sym (Σ-assoc _ _ _ ● Σ-over-Contr-base-is-fib _ _ Contr-f-pσ)) Contr-f-ρτ where

      Contr-f-pσ : isContr (Σ f-p ꞉ p-pres , σ-pres (hrefl _) f-p)
      Contr-f-pσ = ≃-preserves-Contr
        (split , (dep-Σ-UMP A (λ a → f a ≡ f a) λ a f-pa → refl (f a) ≡ (f-pa ∙ refl (f a)) ∙ refl (f a)))
        (Π-preserves-Contr _ (λ a → ≃-preserves-Contr (Σ-preserves-family-≃ (λ f-pa → post-∙-≃ (refl (f a)) (ru f-pa ∙ ru _))) (free-right-endpt-is-Contr _ _)))  

      Contr-f-ρτ : isContr (Σ f-ρ ꞉ ρ-pres (hrefl _) (hrefl _) , τ-pres (hrefl _) (hrefl _) (hrefl _) f-ρ)
      Contr-f-ρτ = ≃-preserves-Contr
        (split , (dep-Σ-UMP A (λ a → refl (f a) ≡ refl _ ∙ refl _ ∙ refl _) λ a f-ρa → refl _ ∙ (refl _ ∙ f-ρa ∙ refl _ ∙ refl _ ∙ refl _ ∙ refl _ ∙ refl _) ≡ refl (refl (f a))))
        (Π-preserves-Contr _ (λ a → ≃-preserves-Contr (Σ-preserves-family-≃ (λ f-ρa → pre-∙-≃ (refl (refl (f a))) (lu _ ⁻¹ ∙ ru _ ⁻¹ ∙ ru _ ⁻¹ ∙ ru _ ⁻¹ ∙ ru _ ⁻¹ ∙ ru _ ⁻¹ ∙ lu f-ρa ⁻¹))) (free-left-endpt-is-Contr _ _)))

  open Preservation-of-Equivalences using (ishae-pres ; hae-pres)

  ishae-pres-is-Contr : (A₁ A₂ : 𝓤 ̇) (e : A₁ ≃ A₂) (B₁ B₂ : 𝓥 ̇) (e' : B₁ ≃ B₂) (f₁ : A₁ → B₁) (f₂ : A₂ → B₂) (f-s : f₂ ∘ pr₁ e ∼ pr₁ e' ∘ f₁) → isContr (ishae-pres A₁  A₂ e B₁ B₂ e' f₁ f₂ f-s)
  ishae-pres-is-Contr {𝓤} {𝓥} = 𝕁-≃ univ (λ A₁ A₂ e → (B₁ B₂ : 𝓥 ̇) (e' : B₁ ≃ B₂) (f₁ : A₁ → B₁) (f₂ : A₂ → B₂) (f-s : f₂ ∘ pr₁ e ∼ pr₁ e' ∘ f₁) → isContr (ishae-pres A₁ A₂ e B₁ B₂ e' f₁ f₂ f-s)) λ A →
    𝕁-≃ univ (λ B₁ B₂ e' → (f₁ : A → B₁) (f₂ : A → B₂) (f-s : f₂ ∘ id ∼ pr₁ e' ∘ f₁) → isContr (ishae-pres A A (≃-refl A) B₁ B₂ e' f₁ f₂ f-s)) λ B f₁ f₂ →
      𝕁-∼ (λ f₂ f₁ f-s → isContr (ishae-pres A A (≃-refl A) B B (≃-refl B) f₁ f₂ f-s)) (λ f → ishae-pres-is-Contr' A B f) f₂ f₁

  hae-pres-≃-fun-pres : (A₁ A₂ : 𝓤 ̇) (e : A₁ ≃ A₂) (B₁ B₂ : 𝓥 ̇) (e' : B₁ ≃ B₂) (f₁ : A₁ → B₁) (f₂ : A₂ → B₂) → hae-pres A₁ A₂ e B₁ B₂ e' f₁ f₂ ≃ (f₂ ∘ pr₁ e ∼ pr₁ e' ∘ f₁)
  hae-pres-≃-fun-pres A₁ A₂ e B₁ B₂ e' f₁ f₂ = Σ-of-Contr-family-is-base _ _ (ishae-pres-is-Contr A₁ A₂ e B₁ B₂ e' f₁ f₂)

  fun-pres-to-hae-pres : {A₁ A₂ : 𝓤 ̇} (e : A₁ ≃ A₂) {B₁ B₂ : 𝓥 ̇} (e' : B₁ ≃ B₂) (f₁ : A₁ → B₁) (f₂ : A₂ → B₂) → (f₂ ∘ pr₁ e ∼ pr₁ e' ∘ f₁) → hae-pres A₁ A₂ e B₁ B₂ e' f₁ f₂
  fun-pres-to-hae-pres {𝓤} {𝓥} {A₁} {A₂} e {B₁} {B₂} e' f₁ f₂ = inv (hae-pres-≃-fun-pres A₁ A₂ e B₁ B₂ e' f₁ f₂)

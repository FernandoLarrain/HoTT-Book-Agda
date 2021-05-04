{-# OPTIONS --without-K --exact-split --safe #-}

open import Ch1.Type-theory
open import Ch2.Homotopy-type-theory
open import Ch3.Sets-and-logic
open import Ch4.Equivalences
open import Ch7.2-UIP-and-Hedberg's-theorem-safe
open import Thesis.Z-Algebras
open import Thesis.Identity-types
open import Thesis.Inductive-Z-Algebras
open import Thesis.Cofiltered

module Thesis.Decidable-equality where


retract-of-decidable-equality : ⦃ fe : FunExt ⦄ {X : 𝓤 ̇} {Y : 𝓥 ̇} → Y ◁ X → decidable-equality X → decidable-equality Y
retract-of-decidable-equality {𝓤} {𝓥} {X} {Y} (f , g , ε) d y₁ y₂ with d (g y₁) (g y₂)
... | inl p = inl (ε y₁ ⁻¹ ∙ ap f p ∙ ε y₂)
... | inr p = inr (λ q → p (ap g q))

+-preserves-decidable-equality : ⦃ fe : FunExt ⦄ {X : 𝓤 ̇} {Y : 𝓥 ̇} → decidable-equality X → decidable-equality Y → decidable-equality (X + Y)
+-preserves-decidable-equality {𝓤} {𝓥} {X} {Y} d e (inl x) (inl x₁) = inv (+-preserves-≃ (path-space-inl X Y x (inl x₁)) (→-preserves-dom-≃ 𝟘 (path-space-inl X Y x (inl x₁)))) (d x x₁)
+-preserves-decidable-equality d e (inl x) (inr y) = inr (lower ∘ pr₁ (path-space-inl _ _ x (inr y)))
+-preserves-decidable-equality d e (inr y) (inl x) = inr (lower ∘ pr₁ (path-space-inr _ _ y (inl x)))
+-preserves-decidable-equality {𝓤} {𝓥} {X} {Y} d e (inr y) (inr y₁) = inv (+-preserves-≃ (path-space-inr X Y y (inr y₁)) (→-preserves-dom-≃ 𝟘 (path-space-inr X Y y (inr y₁)))) (e y y₁)

ℤω-has-decidable-equality : ⦃ fe : FunExt ⦄ → decidable-equality ℤω 
ℤω-has-decidable-equality = retract-of-decidable-equality (ϕ , (ψ , ε)) (+-preserves-decidable-equality (+-preserves-decidable-equality ℕ-has-decidable-equality (𝟙-induction (λ x → (y : 𝟙) → is-decidable (x ≡ y)) (𝟙-induction (λ y → is-decidable (⋆ ≡ y)) (inl (refl ⋆))))) ℕ-has-decidable-equality)

  where

  ψ : ℤω → ℕ + 𝟙 + ℕ
  ψ 0ω = inl (inr ⋆)
  ψ (pos x) = inr x
  ψ (neg x) = inl (inl x)

  ϕ : ℕ + 𝟙 + ℕ → ℤω
  ϕ (inl (inl x)) = neg x
  ϕ (inl (inr x)) = 0ω
  ϕ (inr x) = pos x

  ε : ϕ ∘ ψ ∼ id
  ε 0ω = refl _
  ε (pos x) = refl _
  ε (neg x) = refl _

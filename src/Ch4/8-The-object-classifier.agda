{-# OPTIONS --without-K --exact-split --safe #-}

open import Ch1.Type-theory
open import Ch2.Homotopy-type-theory
open import Ch3.Sets-and-logic
open import Ch4.2-Half-adjoint-equivalences

module Ch4.8-The-object-classifier where


-- Lemma 4.8.1 (fibers of pr₁ are values of type family)

fibs-of-pr₁-are-values : {A : 𝓤 ̇} {B : A → 𝓥 ̇} (a : A) → fib {𝓤 ⊔ 𝓥} {𝓤} {Σ B} pr₁ a ≃ B a
fibs-of-pr₁-are-values {𝓤} {𝓥} {A} {B} a =
  fib pr₁ a
    ≃⟨ ≃-sym (Σ-assoc _ _ _) ⟩
  (Σ x ꞉ A , (B x × (x ≡ a)))
    ≃⟨ Σ-preserves-family-≃ (λ x → ×-swap _ _) ⟩
  (Σ x ꞉ A , ((x ≡ a) × B x))
    ≃⟨ (Σ-assoc _ _ _) ⟩
  (Σ w ꞉ (Σ x ꞉ A , x ≡ a) , B (pr₁ w))
    ≃⟨ Σ-over-Contr-base-is-fib _ _ (free-left-endpt-is-Contr _ _) ⟩
  B a ■


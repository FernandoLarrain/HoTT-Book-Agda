{-# OPTIONS --without-K --exact-split --safe #-}

open import Ch1.Type-theory
open import Ch2.Homotopy-type-theory
open import Ch3.Sets-and-logic
open import Ch4.2-Half-adjoint-equivalences
open import Ch4.5-On-the-definition-of-equivalences

module Ch4.Exercises where


-- Exercise 4.4 (The unstable octahedral axiom).

module _ {A : 𝓤 ̇} {B : 𝓥 ̇} {C : 𝓦 ̇} (f : A → B) (g : B → C) where

  module natural-map (b : B) where

    -- (i).1 Natural map
  
    ϕ : fib (g ∘ f) (g b) → fib g (g b)
    ϕ (a , p) = (f a) , p

    -- (i).2 Fibers over (b , refl (g b))

    F : fib ϕ (b , refl (g b)) → fib f b
    F ((a , p) , q) = a , ap pr₁ q

    G : fib f b → fib ϕ (b , refl (g b))
    G (a , p) = (a , (ap g p)) , dpair-≡ (p , q) where
      q :  transport (λ x → g x ≡ g b) p (ap g p) ≡ refl (g b)
      q = transport-funval-≡ g (λ - → g b) p (ap g p) ∙ (linv _ ⋆' ap-const-fun (g b) p)

    α : F ∘ G ∼ id
    α (a , p) = dpair-≡ (refl a , dpr₁-≡-β p _) 

    β : G ∘ F ∼ id
    β ((a , .(refl (g (f a)))) , refl .(f a , refl (g (f a)))) = refl _

    fibs-of-ϕ : fib ϕ (b , refl (g b)) ≃ fib f b
    fibs-of-ϕ = F , qinv-to-isequiv (G , α , β)

  module fib-of-∘ where

  -- (ii) Classically, (g ∘ f) ⁻¹ [c] = g ⁻¹ [f ⁻¹ [c]]

  fib-of-∘ : (c : C) → fib (g ∘ f) c ≃ (Σ w ꞉ fib g c , fib f (pr₁ w))
  fib-of-∘ c =
    fib (g ∘ f) c
      ≃⟨ (Σ-preserves-family-≃ λ a → ≃-sym (Σ-over-Contr-base-is-fib _ _ (free-right-endpt-is-Contr _ _))) ⟩
    (Σ a ꞉ A , Σ w ꞉ (Σ b ꞉ B , f a ≡ b) , g (pr₁ w) ≡ c)
      ≃⟨ (Σ-preserves-family-≃ λ a → ≃-sym (Σ-assoc _ _ _)) ⟩
    (Σ a ꞉ A , Σ b ꞉ B , (f a ≡ b) × (g b ≡ c))
      ≃⟨ (Σ-preserves-family-≃ λ a → Σ-preserves-family-≃ λ b → ×-swap _ _) ⟩
    (Σ a ꞉ A , Σ b ꞉ B , (g b ≡ c) × (f a ≡ b))
      ≃⟨ Σ-preserves-family-≃ (λ a → Σ-assoc _ _ _) ⟩
    (Σ a ꞉ A , Σ w ꞉ fib g c , f a ≡ pr₁ w)
      ≃⟨ Σ-assoc _ _ _ ● Σ-preserves-base-≃ _ (×-swap _ _) ⟩
    (Σ w ꞉ fib g c × A , f (pr₂ w) ≡ pr₁ (pr₁ w))
      ≃⟨ ≃-sym (Σ-assoc _ _ _) ⟩
    (Σ w ꞉ fib g c , fib f (pr₁ w)) ■

open fib-of-∘ public 

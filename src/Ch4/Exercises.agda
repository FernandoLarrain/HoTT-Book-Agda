{-# OPTIONS --without-K --exact-split #-}

open import Ch1.Type-theory
open import Ch2.Homotopy-type-theory
open import Ch3.Sets-and-logic
open import Ch4.2-Half-adjoint-equivalences
open import Ch4.5-On-the-definition-of-equivalences
open import Ch4.9-Univalence-implies-funext

module Ch4.Exercises where


-- Exercise 2.13 (The type of autoequivalences of 𝟚 is 𝟚).

𝟚-is-Set : isSet 𝟚
𝟚-is-Set ₀ .₀ p (refl .₀) with isequiv-to-qinv (pr₂ (path-space-inl 𝟙 𝟙 ⋆ ₀ ● 𝟙-≡-≃-𝟙 ⋆ ⋆))
... | (g , α , β)  = β p ⁻¹ ∙ β (refl ₀)
𝟚-is-Set ₁ .₁ p (refl .₁) with isequiv-to-qinv (pr₂ (path-space-inr 𝟙 𝟙 ⋆ ₁ ● 𝟙-≡-≃-𝟙 ⋆ ⋆))
... | (g , α , β) = β p ⁻¹ ∙ β (refl ₁)

𝟚-η : {B : 𝟚 → 𝓤 ̇} (f : Π B) → (f ≡ 𝟚-induction B (f ₀) (f ₁))
𝟚-η f = funext (𝟚-induction _ (refl _) (refl _))

𝟚-uniqueness-pple : ⦃ fe : FunExt ⦄ {B : 𝟚 → 𝓤 ̇} (f g : Π B) → f ₀ ≡ g ₀ → f ₁ ≡ g ₁ → f ≡ g
𝟚-uniqueness-pple {𝓤} {B} f g p₀ p₁ = 𝟚-η f ∙ ap (λ - → 𝟚-induction (λ  - → B -) (f ₀) -) p₁ ∙ ap (λ - → 𝟚-induction (λ  - → B -) - (g ₁)) p₀ ∙ 𝟚-η g ⁻¹

module autoequivs-of-𝟚 where

  -- Autoequivalences of 𝟚:

  twist : 𝟚 → 𝟚
  twist ₀ = ₁
  twist ₁ = ₀

  twist-is-not-id : ¬ (twist ≡ id)
  twist-is-not-id p = ₀-is-not-₁ (happly p ₁)

  twist-≃ : 𝟚 ≃ 𝟚
  twist-≃ =
    twist ,
    qinv-to-isequiv (
      twist ,
      (𝟚-induction _ (refl _) (refl _)) ,
      (𝟚-induction _ (refl _) (refl _))
      )

  twist-≃-is-not-≃-refl : ¬ (twist-≃ ≡ ≃-refl 𝟚)
  twist-≃-is-not-≃-refl p = twist-is-not-id (ap pr₁ p)

  -- A quasi-inverse:

  ϕ : (𝟚 ≃ 𝟚) → 𝟚
  ϕ e = pr₁ e ₀

  ψ : 𝟚 → (𝟚 ≃ 𝟚)
  ψ ₀ = ≃-refl 𝟚
  ψ ₁ = twist-≃

  α : ϕ ∘ ψ ∼ id
  α ₀ = refl ₀
  α ₁ = refl ₁

  β : ψ ∘ ϕ ∼ id
  β (f , g , η , ε , τ) with f ₀ | f ₁ | 𝟚-η f
  ... | ₀ | ₀ | refl _ = !𝟘 _ (₀-is-not-₁ (η ₀ ⁻¹ ∙ η ₁))
  ... | ₀ | ₁ | refl _ = Σ-over-predicate ishae-is-Prop (𝟚-uniqueness-pple _ _ (refl _) (refl _))
  ... | ₁ | ₀ | refl _ = Σ-over-predicate ishae-is-Prop (𝟚-uniqueness-pple _ _ (refl _) (refl _))
  ... | ₁ | ₁ | refl _ = !𝟘 _ (₀-is-not-₁ (η ₀ ⁻¹ ∙ η ₁))

  -- An equivalence:

  autoequivs-of-𝟚 : (𝟚 ≃ 𝟚) ≃ 𝟚
  autoequivs-of-𝟚 = ϕ , qinv-to-isequiv (ψ , α , β)

  -- Classification of the autoequivalences:

  𝟚-autoequiv-classification : (e : 𝟚 ≃ 𝟚) → (e ≡ ≃-refl 𝟚) + (e ≡ twist-≃)
  𝟚-autoequiv-classification e with ϕ e | β e
  ... | ₀ | refl _ = inl (refl _)
  ... | ₁ | refl _ = inr (refl _)

open autoequivs-of-𝟚 using (twist ; twist-is-not-id ; twist-≃ ; twist-≃-is-not-≃-refl ; autoequivs-of-𝟚 ; 𝟚-autoequiv-classification) public


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
      q = transport-funval-≡ g (λ - → g b) p (ap g p) ∙ (linv _ ✦ ap-const-fun (g b) p)

    α : F ∘ G ∼ id
    α (a , p) = dpair-≡ (refl a , dpr₁-≡-β p _) 

    β : G ∘ F ∼ id
    β ((a , .(refl (g (f a)))) , refl .(f a , refl (g (f a)))) = refl _

    fibs-of-ϕ : fib ϕ (b , refl (g b)) ≃ fib f b
    fibs-of-ϕ = F , qinv-to-isequiv (G , α , β)

  module fib-∘ where

  -- (ii) Classically, (g ∘ f) ⁻¹ [c] = g ⁻¹ [f ⁻¹ [c]]

  fib-∘ : (c : C) → fib (g ∘ f) c ≃ (Σ w ꞉ fib g c , fib f (pr₁ w))
  fib-∘ c =
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

open fib-∘ public 

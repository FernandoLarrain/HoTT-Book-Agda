{-# OPTIONS --without-K --exact-split --safe #-}

open import Ch1.Type-theory
open import Ch2.Homotopy-type-theory
open import Ch3.Sets-and-logic
open import Ch4.Equivalences
open import Thesis.Z-Algebras
open import Thesis.Identity-types
open import Thesis.Inductive-Z-Algebras

module Thesis.ZAlg-is-Cofiltered where


-- XIII. Cones

-- Over pairs of objects.

_⨂_ : Alg 𝓤 → Alg 𝓤 → Alg 𝓤
(A , a₀ , (s , p , σ , ρ , τ)) ⨂ (B , b₀ , (s' , p' , σ' , ρ' , τ')) = (A × B) , (a₀ , b₀) , ((Σ-induction (λ a b → s a , s' b)) , qinv-to-isequiv ((Σ-induction (λ a b → p a , p' b)) , (Σ-induction λ a b → pair-≡ (ρ a , ρ' b)) , (Σ-induction λ a b → pair-≡ (σ a , σ' b))))

proj₁ : (A B : Alg 𝓤) → Hom (A ⨂ B) A
proj₁ A B = pr₁ , ((refl _) , (hrefl _))

proj₂ : (A B : Alg 𝓤) → Hom (A ⨂ B) B
proj₂ A B = pr₂ , ((refl _) , (hrefl _))

-- In fact, we have binary products.

⨂-UMP : ⦃ fe : FunExt ⦄ (A B C : Alg 𝓤) → Hom C (A ⨂ B) ≃ Hom C A × Hom C B
⨂-UMP {𝓤} A B C = ϕ , qinv-to-isequiv (ψ , ϕ∘ψ , ψ∘ϕ) where
  ϕ : Hom C (A ⨂ B) → Hom C A × Hom C B
  ϕ f = comp C (A ⨂ B) A (proj₁ A B) f , comp C (A ⨂ B) B (proj₂ A B) f
  ψ : Hom C A × Hom C B → Hom C (A ⨂ B)
  ψ ((g , g₀ , g-s) , (h , h₀ , h-s)) = (λ c → g c , h c) , ((pair-≡ (g₀ , h₀)) , (λ c → pair-≡ (g-s c , h-s c)))
  ϕ∘ψ : ϕ ∘ ψ ∼ id
  ϕ∘ψ ((g , g₀ , g-s) , (h , h₀ , h-s)) = pair-≡ (Hom-≡-intro C A _ _ ((hrefl _) , (rinv g₀ ⁻¹ ∙ (((ap-pr₁-β g₀ h₀) ⁻¹ ∙ ru _) ∙ᵣ g₀ ⁻¹)) , λ c → rinv (g-s c) ⁻¹ ∙ (((ap-pr₁-β (g-s c) (h-s c)) ⁻¹ ∙ ru _ ∙ ru _) ∙ᵣ g-s c ⁻¹)) , Hom-≡-intro C B _ _ ((hrefl _) , (rinv h₀ ⁻¹ ∙ (((ap-pr₂-β g₀ h₀) ⁻¹ ∙ ru _) ∙ᵣ h₀ ⁻¹)) , λ c → rinv (h-s c) ⁻¹ ∙ (((ap-pr₂-β (g-s c) (h-s c)) ⁻¹ ∙ ru _ ∙ ru _) ∙ᵣ h-s c ⁻¹)))
  ψ∘ϕ : ψ ∘ ϕ ∼ id
  ψ∘ϕ (f , f₀ , f-s) = dpair-≡ ((refl _) , (pair-≡ ((ap (λ - → pair-≡ (- , (ap pr₂ f₀ ∙ refl _))) (ru _ ⁻¹) ∙ (ap (λ - → pair-≡ (ap pr₁ f₀ , -)) (ru _ ⁻¹) ∙ pr-≡-η _)) , funext (λ c → ap (λ - → pair-≡ (- , (ap pr₂ (f-s c) ∙ refl _))) (ru _ ⁻¹) ∙ (ap (λ - → pair-≡ (ap pr₁ (f-s c) , -)) (ru _ ⁻¹) ∙ pr-≡-η _)))))


-- Over pairs of parallel arrows.

module _ ⦃ fe : FunExt ⦄ where

  Eqz : (A B : Alg 𝓤) → Hom A B → Hom A B → Alg 𝓤
  Eqz A B f g = TotAlg A (depEqz A (ConstFibAlg A B) f g)

  Eqz-map : (A B : Alg 𝓤) (f g : Hom A B) → Hom (Eqz A B f g) A
  Eqz-map A B f g = pr₁ , refl _ , hrefl _

  Eqz-equalizes' : (A B : Alg 𝓤) (f g : Hom A B) → HomId (Eqz A B f g) B (comp (Eqz A B f g) A B f (Eqz-map A B f g)) (comp (Eqz A B f g) A B g (Eqz-map A B f g))
  Eqz-equalizes' (A , a₀ , s , i) (B , b₀ , s' , j) (f , f₀ , f-s) (g , g₀ , g-s) = pr₂ , (((lu _ ∙ᵣ (g₀ ⁻¹)) ∙ ((refl _ ∙ f₀) ∙ₗ (ap _⁻¹ (lu _)))) , Σ-induction λ a q → ap (λ - → - ∙ ap s' q ∙ g-s a ⁻¹) (lu _) ∙ ((refl _ ∙ f-s a ∙ ap s' q) ∙ₗ ap _⁻¹ (lu _)))

  Eqz-equalizes : (A B : Alg 𝓤) (f g : Hom A B) → comp (Eqz A B f g) A B f (Eqz-map A B f g) ≡ comp (Eqz A B f g) A B g (Eqz-map A B f g)
  Eqz-equalizes A B f g = Hom-≡-intro (Eqz A B f g) B _ _ (Eqz-equalizes' A B f g)

  -- Unfortunately, what follows is not quite a proof that Eqz is an equalizer. So we only have cones over pairs of parallel arrows.

  Eqz-UMP : (A B C : Alg 𝓤) (f g : Hom A B) → Hom C (Eqz A B f g) ≃ (Σ h ꞉ Hom C A , comp C A B f h ≡ comp C A B g h)
  Eqz-UMP {𝓤} (A , a₀ , s , i) (B , b₀ , s' , i') (C , c₀ , t , j) (f , f₀ , f-s) (g , g₀ , g-s) =
    _
      ≃⟨ lemma4 ⟩
    Regroup
      ≃⟨ ≃-sym lemma1 ⟩
    ((Σ h' ꞉ Hom C' A' , HomId C' B' (comp C' A' B' f' h') (comp C' A' B' g' h')))
      ≃⟨ Σ-preserves-family-≃ (λ h' → ≃-sym (IdHom-≃-HomId C' B' (comp C' A' B' f' h') (comp C' A' B' g' h'))) ⟩
    (Σ h' ꞉ Hom C' A' , comp C' A' B' f' h' ≡ comp C' A' B' g' h') ■
    where

    A' B' C' E' : Alg 𝓤
    A' = (A , a₀ , s , i)
    B' = (B , b₀ , s' , i')
    C' = (C , c₀ , t , j)
    f' g' : Hom A' B'
    f' = (f , f₀ , f-s)
    g' = (g , g₀ , g-s)
    E' = (Eqz A' B' f' g')
    E = pr₁ E'
    e₀ = pr₁ (pr₂ E')
    t' = pr₁ (pr₂ (pr₂ E'))
    j' = pr₂ (pr₂ (pr₂ E'))
    m' : Hom E' A'
    m' = Eqz-map A' B' f' g'
    m = pr₁ m'
    m₀ = pr₁ (pr₂ m')
    m-s = pr₂ (pr₂ m')
    meq' = Eqz-equalizes' A' B' f' g'
    meq = pr₁ meq'

    Regroup : 𝓤 ̇
    Regroup = Σ w ꞉ (Σ h ꞉ (C → A) , f ∘ h ∼ g ∘ h) , (Σ h₀ ꞉ (pr₁ w) c₀ ≡ a₀ , (pr₂ w) c₀ ≡ ap f h₀ ∙ f₀ ∙ (ap g h₀ ∙ g₀) ⁻¹) × (Σ h-s ꞉ (pr₁ w) ∘ t ∼ s ∘ (pr₁ w) , ((c : C) → (pr₂ w) (t c) ≡ ap f (h-s c) ∙ f-s ((pr₁ w) c) ∙ ap s' ((pr₂ w) c) ∙ (ap g (h-s c) ∙ g-s ((pr₁ w) c)) ⁻¹))

    lemma1 : (Σ h' ꞉ Hom C' A' , HomId C' B' (comp C' A' B' f' h') (comp C' A' B' g' h')) ≃ Regroup
    lemma1 = ϕ , qinv-to-isequiv (ψ , hrefl _ , hrefl _)
      where
      ϕ : (Σ h' ꞉ Hom C' A' , HomId C' B' (comp C' A' B' f' h') (comp C' A' B' g' h')) → Regroup
      ϕ ((h , h₀ , h-s) , (q , q₀ , q-s)) = (h , q) , (h₀ , q₀) , (h-s , q-s)
      ψ : Regroup → (Σ h' ꞉ Hom C' A' , HomId C' B' (comp C' A' B' f' h') (comp C' A' B' g' h'))
      ψ ((h , q) , (h₀ , q₀) , (h-s , q-s)) = ((h , h₀ , h-s) , (q , q₀ , q-s))

    ϕ : (C → pr₁ (Eqz A' B' f' g')) → Σ h ꞉ (C → A) , f ∘ h ∼ g ∘ h  
    ϕ u = pr₁ ∘ u , meq ∘ u
    ψ : (Σ h ꞉ (C → A) , f ∘ h ∼ g ∘ h) → (C → pr₁ (Eqz A' B' f' g'))
    ψ (h , q) c = (h c) , (q c)
    ϕ∘ψ : ϕ ∘ ψ ∼ id
    ϕ∘ψ = hrefl _
    ψ∘ϕ : ψ ∘ ϕ ∼ id
    ψ∘ϕ = hrefl _

    lemma2 : (a : A) (p : f a ≡ g a) (h₀ : a ≡ a₀) → (transport (λ - → f - ≡ g -) h₀ p ≡ f₀ ∙ g₀ ⁻¹) ≃ (p ≡ (ap f h₀ ∙ f₀ ∙ (ap g h₀ ∙ g₀) ⁻¹))
    lemma2 a p (refl .a) = post-∙-≃ p (ap (λ - → f₀ ∙ - ⁻¹) (lu g₀) ∙ lu _ ∙ ∙-assoc _ _ _)

    lemma3 : {b₀ b₁ b₂ b₃ b₄ b₅ : B} (p₁ : b₀ ≡ b₁) (p₂ : _ ≡ b₂) (p₃ : _ ≡ b₃) (p₄ : _ ≡ b₄) (p₅ : _ ≡ b₅) (p₆ : _ ≡ _) → (p₁ ⁻¹ ∙ p₂ ∙ p₃ ≡ p₄ ∙ p₅ ∙ p₆ ⁻¹) ≃ (p₂ ≡ p₁ ∙ p₄ ∙ p₅ ∙ (p₃ ∙ p₆) ⁻¹) 
    lemma3 {b₀} {.b₀} {.b₀} {.b₀} {.b₀} {.b₀} (refl .b₀) p₂ (refl .b₀) (refl .b₀) (refl .b₀) (refl .b₀) = pre-∙-≃ _ (lu _ ∙ ru _)

    lemma4 : Hom C' (Eqz A' B' f' g') ≃ Regroup
    lemma4 = Σ-preserves-≃' _ _ (ϕ , qinv-to-isequiv (ψ , hrefl _ , hrefl _)) (Σ-induction λ h q → ×-preserves-≃
        (Σ-≡-≃ ● Σ-preserves-family-≃ (λ h₀ → lemma2 (h c₀) (q c₀) h₀))
        (Π-preserves-family-≃ (λ c →
          Σ-≡-≃ ● Σ-preserves-family-≃ (λ h-sc →
            (pre-∙-≃ _ (transport-funval-≡ f g h-sc (q (t c)) ⁻¹)) ●
            lemma3 _ _ _ _ _ _)) ●
          split , (dep-Σ-UMP C _ (λ c h-sc → q (t c) ≡ ap f h-sc ∙ f-s (h c) ∙ ap s' (q c) ∙ (ap g h-sc ∙ g-s (h c)) ⁻¹))))

  -- Previous equivalence is precomposition by equalizer:

  Eqz-UMP-is-precomp : (A B C : Alg 𝓤) (f g : Hom A B) → pr₁ ∘ (pr₁ (Eqz-UMP A B C f g)) ∼ comp C (Eqz A B f g) A (Eqz-map A B f g)
  Eqz-UMP-is-precomp {𝓤} (A , a₀ , s , i) (B , b₀ , s' , i') (C , c₀ , t , j) (f , f₀ , f-s) (g , g₀ , g-s) (u , u₀ , u-s) = dpair-≡ ((refl _) , (pair-≡ ((ap pr₁ (dpr-≡-agreement u₀) ∙ ru _) , funext (λ c → ap pr₁ (dpr-≡-agreement (u-s c)) ∙ ru _))))

{-# OPTIONS --without-K --exact-split --rewriting #-}

open import Ch1.Type-theory
open import Ch2.Homotopy-type-theory
open import Ch3.Sets-and-logic
open import Ch4.Equivalences
open import Rewrite

module Ch6.8-Pushouts where


-- Definition of (homotopy) pushout.

postulate

  -- (i) Type formation rule

  _⊔⟨_⟩_ : (A : 𝓤 ̇) (C : 𝓦 ̇) (B : 𝓥 ̇) → (C → A) → (C → B) → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ̇

po : {A : 𝓤 ̇} {B : 𝓥 ̇} {C : 𝓦 ̇}  → (C → A) → (C → B) → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ̇
po {𝓤} {𝓥} {𝓦} {A} {B} {C} f g = (A ⊔⟨ C ⟩ B) f g  

module _ {A : 𝓤 ̇} {B : 𝓥 ̇} {C : 𝓦 ̇} (f : C → A) (g : C → B) where

  postulate

    -- (ii) Constructors

    inlₚ : A → po f g
    inrₚ : B → po f g
    glue : inlₚ ∘ f ∼ inrₚ ∘ g  
    
  module _ (D : po f g → 𝓣 ̇) (i : (a : A) → D (inlₚ a)) (j : (b : B) → D (inrₚ b)) (γ : (c : C) → i (f c) ≡ j (g c) [ D ↓ glue c ]) where

    postulate

      -- (iii) Induction principle

      po-ind : Π D
  
      -- (iv) Computation rules

      i-β : (a : A) → po-ind (inlₚ a) ↦ i a
      
      {-# REWRITE i-β #-}

      j-β : (b : B) → po-ind (inrₚ b) ↦ j b

      {-# REWRITE j-β #-}

      γ-β : (c : C) → apd po-ind (glue c) ≡ γ c


  module _ (D : 𝓣 ̇) (i : A → D) (j : B → D) (γ : i ∘ f ∼ j ∘ g) where

    -- (v) Recursion principle
  
    po-rec : po f g → D
    po-rec = po-ind (λ x → D) i j λ c → transportconst D (glue c) (i (f c)) ∙ γ c
    -- (vi) Computation rules

    i-β' : (a : A) → po-rec (inlₚ a) ≡ i a
    i-β' a = refl (i a)

    j-β' : (b : B) → po-rec (inrₚ b) ≡ j b
    j-β' b = refl (j b)

    γ-β' : (c : C) → ap po-rec (glue c) ≡ γ c
    γ-β' c = ∙ₗ-inv _ _ _ (apdconst D po-rec (glue c) ⁻¹ ∙ γ-β (λ x → D) i j γ' c) 
      where
      γ' : (c : C) → i (f c) ≡ j (g c) [ (λ x → D) ↓ glue c ]
      γ' c = transportconst D (glue c) (i (f c)) ∙ γ c


  -- (vii) Uniqueness principle

  po-η' : ⦃ fe : FunExt ⦄ {D : 𝓣 ̇} (s : po f g → D) → po-rec D (s ∘ inlₚ) (s ∘ inrₚ) (λ c → ap s (glue c)) ≡ s
  po-η' s = funext (po-ind _ (λ a → refl _) (λ b → refl _) λ c → transport-funval-≡ _ _ (glue c) (refl _) ∙ (((ru _ ⁻¹ ∙  ap _⁻¹ (γ-β' _ (s ∘ inlₚ) (s ∘ inrₚ) (λ c → ap s (glue c)) c)) ∙ᵣ ap s (glue c)) ∙ linv _))

  po-uniqueness-pple : ⦃ fe : FunExt ⦄ {D : 𝓣 ̇} (s s' : po f g → D) (α : s ∘ inlₚ ∼ s' ∘ inlₚ) (β : s ∘ inrₚ ∼ s' ∘ inrₚ) → ((c : C) → α (f c) ∙ ap s' (glue c) ≡ ap s (glue c) ∙ β (g c)) → s ≡ s'   
  po-uniqueness-pple {𝓣} {D} s s' α β θ = funext (po-ind _ α β (λ c → transport-funval-≡ s s' (glue c) (α (f c)) ∙ (∙-assoc _ _ _ ⁻¹ ∙ ((ap s (glue c) ⁻¹ ∙ₗ (θ c)) ∙ ∙-assoc _ _ _ ∙ (linv _ ∙ᵣ β (g c)) ∙ lu _ ⁻¹))))


  -- Definition 6.8.1 (cocone under a span)

  cocone : 𝓣 ̇ →  𝓤 ⊔ 𝓥 ⊔ 𝓦 ⊔ 𝓣 ̇
  cocone D = Σ i ꞉ (A → D) , Σ j ꞉ (B → D) , i ∘ f ∼ j ∘ g


  -- Lemma 6.8.2 (UMP of pushout)

  module po-UMP ⦃ fe : FunExt ⦄ (E : 𝓣 ̇) where

    c⊔ : (po f g → E) → cocone E
    c⊔ t = t ∘ inlₚ , t ∘ inrₚ , λ c → ap t (glue c) 

    po-rec' : cocone E → po f g → E
    po-rec' (i , j , h) = po-rec E i j h

    c⊔∘po-rec' : c⊔ ∘ po-rec' ∼ id
    c⊔∘po-rec' (i , j , h) = dpair-≡ ((refl i) , (dpair-≡ ((refl j) , (funext λ c → γ-β' E i j h c ))))

    po-rec'∘c⊔ :  po-rec' ∘ c⊔ ∼ id
    po-rec'∘c⊔ t = po-uniqueness-pple _ _ (hrefl _) (hrefl _) λ c → lu _ ⁻¹ ∙ (γ-β' E (t ∘ inlₚ) (t ∘ inrₚ) _ c ⁻¹ ∙ ru _)

    po-UMP : (po f g → E) ≃ cocone E
    po-UMP = c⊔ , (qinv-to-isequiv (po-rec' , c⊔∘po-rec' , po-rec'∘c⊔))

-- TO DO: Examples (suspension, join, cofiber, wedge and smash product as pushouts)

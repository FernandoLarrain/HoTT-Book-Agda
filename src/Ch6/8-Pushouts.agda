{-# OPTIONS --without-K --exact-split --rewriting #-}

open import Ch1.Type-theory
open import Ch2.Homotopy-type-theory
open import Ch3.Sets-and-logic
open import Ch4.Equivalences
open import Ch6.9-Truncations
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

    equiv : (po f g → E) ≃ cocone E
    equiv = c⊔ , (qinv-to-isequiv (po-rec' , c⊔∘po-rec' , po-rec'∘c⊔))


  -- Lemma 6.9.3 (Set pushout).

  Set-po-UMP : ⦃ fe : FunExt ⦄ ⦃ st : SetTrunc ⦄ {E : 𝓣 ̇} → isSet A → isSet B → isSet C → isSet E → (∥ po f g ∥₀ → E) ≃ cocone E
  Set-po-UMP {𝓣} {E} x x₁ x₂ x₃ = ∥∥₀-UMP.equiv _ x₃ ● po-UMP.equiv E


-- TO DO: Examples (suspension, join, cofiber, wedge and smash product as pushouts)

-- Definition (join).

_*_ : 𝓤 ̇ → 𝓥 ̇ → 𝓤 ⊔ 𝓥 ̇
A * B = (A ⊔⟨ A × B ⟩ B) pr₁ pr₂


-- -- Lemma 8.5.9 (Join is associative).

-- module *-assoc ⦃ fe : FunExt ⦄ (A : 𝓤 ̇) (B : 𝓥 ̇) (C : 𝓦 ̇) where

--   -- A * B
  
--   i₁ : A → A * B
--   i₁ = inlₚ pr₁ pr₂

--   i₂ : B → A * B
--   i₂ = inrₚ pr₁ pr₂

--   glueAB : i₁ ∘ pr₁ ∼ i₂ ∘ pr₂
--   glueAB = glue pr₁ pr₂

--   -- (A * B) * C

--   l₁ : A * B → (A * B) * C
--   l₁ = inlₚ pr₁ pr₂

--   l₂ : C → (A * B) * C
--   l₂ = inrₚ pr₁ pr₂

--   glue-left : l₁ ∘ pr₁ ∼ l₂ ∘ pr₂
--   glue-left = glue pr₁ pr₂

--   -- B * C

--   j₁ : B → B * C
--   j₁ = inlₚ pr₁ pr₂

--   j₂ : C → B * C
--   j₂ = inrₚ pr₁ pr₂

--   glueBC : j₁ ∘ pr₁ ∼ j₂ ∘ pr₂
--   glueBC = glue pr₁ pr₂

--   -- A * (B * C)

--   r₁ : A → A * (B * C)
--   r₁ = inlₚ pr₁ pr₂

--   r₂ : B * C → A * (B * C)
--   r₂ = inrₚ pr₁ pr₂

--   glue-right : r₁ ∘ pr₁ ∼ r₂ ∘ pr₂
--   glue-right = glue pr₁ pr₂


--   -- Quasi-inverse

--   f : (A * B) * C → A * (B * C)
--   f = po-rec _ _ _ f₁ f₂ (Σ-induction (po-ind _ _
--       (λ (z : A * B) → (c : C) → f₁ z ≡ f₂ c)
--       (λ a c → glue-right (a , j₂ c))
--       (λ b c → ap r₂ (glueBC (b , c)))
--       (Σ-induction (λ a b →
--         aux-path a b
--         ))
--       )
--     )
--     where
--     f₁ : A * B → A * (B * C)
--     f₁ = po-rec _ _ _ r₁ (r₂ ∘ j₁) (Σ-induction λ a b → glue-right (a , j₁ b))
--     f₂ : C → A * (B * C)
--     f₂ = r₂ ∘ j₂
--     transport-lemma : {x y : A * B} (p : x ≡ y) (g : (c : C) → f₁ x ≡ f₂ c) → transport (λ z → (c : C) → f₁ z ≡ f₂ c) p g ∼ λ c → ap f₁ p ⁻¹ ∙ g c
--     transport-lemma (refl _) g c = lu _
--     aux-path : (a : A) (b : B) → transport (λ z → (c : C) → f₁ z ≡ f₂ c) (glueAB (a , b)) (λ c → glue-right (a , j₂ c)) ≡ (λ c → ap r₂ (glueBC (b , c)))
--     aux-path a b = funext (λ c → transport-lemma (glueAB (a , b)) (λ c → glue-right (a , j₂ c)) c ∙ {!!}) -- apd (λ x → glue-right (a , x)) (glueBC (b , c)) needs a similar transport lemma.

--   -- Equivalence

--   equiv : (A * B) * C ≃ A * (B * C)
--   equiv = {!!}


{-# OPTIONS --without-K --exact-split --rewriting #-}

open import Ch1.Type-theory
open import Ch2.Homotopy-type-theory
open import Ch3.Sets-and-logic
open import Ch4.Equivalences
open import Rewrite
open import Ch6.2-Induction-pples-and-dependent-paths

module Ch6.5-Suspensions where


-- The suspension of a type A, Susp A.

postulate

  -- (i) Type formation rule

  Susp : (A : 𝓤 ̇) →  𝓤 ̇

  -- (ii) Constructors
  
  north : {A : 𝓤 ̇} → Susp A
  south : {A : 𝓤 ̇} → Susp A
  merid : {A : 𝓤 ̇} → A → Id (Susp A) north south

module _ {A : 𝓤 ̇} (P : Susp A → 𝓥 ̇) (n : P north) (s : P south) (m : (a : A) → n ≡ s [ P ↓ merid a ]) where

  postulate

    -- (iii) Induction principle

    Susp-ind : Π P
  
    -- (iv) Computation rules

    north-β : Susp-ind north ↦ n

    {-# REWRITE north-β #-}

    south-β : Susp-ind south ↦ s

    {-# REWRITE south-β #-}

    merid-β : (a : A) → apd Susp-ind (merid a) ≡ m a  

module _ {A : 𝓤 ̇} {B : 𝓥 ̇} (n : B) (s : B) (m : A → n ≡ s) where

  -- (v) Recursion principle
  
  Susp-rec : Susp A → B
  Susp-rec = Susp-ind (λ x → B) n s λ a → transportconst B (merid a) n ∙ m a 

  -- (vi) Computation rules
  
  north-β' : Susp-rec north ≡ n
  north-β' = refl n

  south-β' : Susp-rec south ≡ s
  south-β' = refl s

  merid-β' : (a : A) → ap Susp-rec (merid a) ≡ m a 
  merid-β' a =  ∙ₗ-inv _ _ _ (apdconst B Susp-rec (merid a) ⁻¹ ∙ merid-β (λ x → B) n s (λ a → transportconst B (merid a) n ∙ m a) a)


-- Lemma 6.5.1 (the circle is the suspension of 𝟚) (TO DO)

-- Susp-𝟚-≃-𝕊¹ : Susp 𝟚 ≃ 𝕊¹
-- Susp-𝟚-≃-𝕊¹ = {!!}


-- Equation 6.5.2 (definition of n-sphere).

-- (i) Iterated pointed suspension

Susp⊙^ : ℕ → (A : 𝓤 ⊙) → 𝓤 ⊙
Susp⊙^ zero (A , a) = A , a
Susp⊙^ (succ n) A = (Susp (pr₁ (Susp⊙^ n A))) , north

-- (ii) Based n-sphere

Sphere⊙ : ℕ → 𝓤₀ ⊙
Sphere⊙ n = Susp⊙^ n (𝟚 , ₁)

-- (iii) n-sphere

Sphere : ℕ → 𝓤₀ ̇
Sphere = pr₁ ∘ Sphere⊙

base : (n : ℕ) → Sphere n
base = pr₂ ∘ Sphere⊙


-- Lemma 6.5.3

open import Ch6.5-Suspensions-safe public


-- Exercise 6.11 (UMP of Susp).

module Susp-UMP ⦃ fe : FunExt ⦄ (A : 𝓤 ̇) (B : 𝓥 ̇) where 

  ϕ : (Susp A → B) → (Σ bₙ ꞉ B , Σ bₛ ꞉ B , (A → bₙ ≡ bₛ)) 
  ϕ f = f north , f south , ap f ∘ merid 

  ψ : (Σ bₙ ꞉ B , Σ bₛ ꞉ B , (A → bₙ ≡ bₛ)) → (Susp A → B)
  ψ (bₙ , bₛ , m) = Susp-rec bₙ bₛ m

  ϕ∘ψ : ϕ ∘ ψ ∼ id
  ϕ∘ψ (bₙ , bₛ , m) = dpair-≡ (refl bₙ , dpair-≡ (refl bₛ , funext (merid-β' bₙ bₛ m)))

  ψ∘ϕ : ψ ∘ ϕ ∼ id
  ψ∘ϕ f = let
    bₙ : B
    bₙ = pr₁ (ϕ f)
    bₛ : B
    bₛ = pr₁ (pr₂ (ϕ f))
    m : (a : A) → bₙ ≡ bₛ
    m = pr₂ (pr₂ (ϕ f))
    in funext (Susp-ind (λ x → (ψ ∘ ϕ) f x ≡ f x) (refl _) (refl _) λ a → transport-funval-≡ (ψ (ϕ f)) f (merid a) (refl (ψ (ϕ f) north)) ∙ (ru _ ⁻¹ ∙ᵣ ap f (merid a)) ∙ (ap (λ - → - ⁻¹ ∙ ap f (merid a)) (merid-β' bₙ bₛ m a) ∙ linv _))
  
  equiv : (Susp A → B) ≃ (Σ bₙ ꞉ B , Σ bₛ ꞉ B , (A → bₙ ≡ bₛ)) 
  equiv =
    ϕ ,
    (qinv-to-isequiv (
      ψ ,
      ϕ∘ψ ,
      ψ∘ϕ
      )
    ) 


-- Lemma 6.5.4 (Susp ⊣ Ω)

module Susp⊣Ω ⦃ fe : FunExt ⦄ (A' : 𝓤 ⊙) (B' : 𝓥 ⊙) where

  A = pr₁ A'
  a₀ = pr₂ A'
  B = pr₁ B'
  b₀ = pr₂ B'

  equiv : Map⊙ (Susp A , north) B' ≃ Map⊙ A' (Ω B')
  equiv =
    Map⊙ (Susp A , north) B'
      ≃⟨ Σ-preserves-base-≃ _ (Susp-UMP.equiv A B) ⟩
    (Σ w ꞉ (Σ bₙ ꞉ B , Σ bₛ ꞉ B , (A → bₙ ≡ bₛ)) , pr₁ w ≡ b₀)
      ≃⟨ ≃-sym (Σ-assoc _ _ _) ⟩
    (Σ bₙ ꞉ B , ((Σ bₛ ꞉ B , (A → bₙ ≡ bₛ)) × (bₙ ≡ b₀)))
      ≃⟨ Σ-preserves-family-≃ (λ bₙ → ≃-sym (Σ-assoc _ _ _)) ⟩
    (Σ bₙ ꞉ B , (Σ bₛ ꞉ B , ((A → bₙ ≡ bₛ) × (bₙ ≡ b₀))))
      ≃⟨ Σ-preserves-family-≃ (λ bₙ → Σ-preserves-family-≃ (λ bₛ → ×-swap _ _)) ⟩
    (Σ bₙ ꞉ B , (Σ bₛ ꞉ B , ((bₙ ≡ b₀) × (A → bₙ ≡ bₛ))))
      ≃⟨ Σ-preserves-family-≃ (λ bₙ → Σ-assoc _ _ _) ⟩
    (Σ bₙ ꞉ B , Σ w ꞉ (B × (bₙ ≡ b₀)) , (A → bₙ ≡ pr₁ w))
      ≃⟨ Σ-preserves-family-≃ (λ bₙ → Σ-preserves-base-≃ _ (×-swap _ _)) ⟩
    (Σ bₙ ꞉ B , Σ w ꞉ ((bₙ ≡ b₀) × B) , (A → bₙ ≡ pr₂ w)) 
      ≃⟨ Σ-assoc _ _ _ ⟩
    (Σ w ꞉ (Σ bₙ ꞉ B , (bₙ ≡ b₀) × B) , (A → pr₁ w ≡ pr₂ (pr₂ w)))
      ≃⟨ Σ-preserves-base-≃ _ (Σ-assoc _ _ _) ⟩
    (Σ w ꞉ (Σ bₙ ꞉ B , (bₙ ≡ b₀)) × B , (A → pr₁ (pr₁ w) ≡ pr₂ w) )
      ≃⟨ ≃-sym (Σ-assoc _ _ _) ⟩
    (Σ w ꞉ (Σ bₙ ꞉ B , (bₙ ≡ b₀)) , Σ bₛ ꞉ B , (A → pr₁ w ≡ bₛ))
      ≃⟨ Σ-over-Contr-base-is-fib _ _ (free-left-endpt-is-Contr _ _) ⟩
    (Σ bₛ ꞉ B , (A → b₀ ≡ bₛ))
      ≃⟨ ≃-sym (Σ-of-Contr-family-is-base _ _ (λ w → free-right-endpt-is-Contr _ _)) ⟩
    (Σ w ꞉ (Σ bₛ ꞉ B , (A → b₀ ≡ bₛ)) , Σ q ꞉ b₀ ≡ (pr₁ w) , (pr₂ w) a₀ ≡ q )
      ≃⟨ ≃-sym (Σ-assoc _ _ _) ⟩
    (Σ bₛ ꞉ B , Σ g ꞉ (A → b₀ ≡ bₛ) , Σ q ꞉ b₀ ≡ bₛ , g a₀ ≡ q)
      ≃⟨ Σ-preserves-family-≃ (λ bₛ → ≃-sym (Σ-swap _ _ _)) ⟩
    (Σ bₛ ꞉ B , Σ q ꞉ b₀ ≡ bₛ , Σ g ꞉ (A → b₀ ≡ bₛ) , g a₀ ≡ q)
      ≃⟨ Σ-assoc _ _ _ ⟩
    (Σ w ꞉ (Σ bₛ ꞉ B , (b₀ ≡ bₛ)) , Σ g ꞉ (A → b₀ ≡ pr₁ w) , g a₀ ≡ pr₂ w)
      ≃⟨ Σ-over-Contr-base-is-fib _ _ (free-right-endpt-is-Contr _ _) ⟩
    Map⊙ A' (Ω B') ■


-- Corollary (UMP of n-sphere).

Sphere-UMP : ⦃ fe : FunExt ⦄ (n : ℕ) (B : 𝓤 ⊙) → Map⊙ (Sphere⊙ n) B ≃ pr₁ (Ω^ n B)
Sphere-UMP zero B = based-maps-≃-unbased-maps.equivalence 𝟙 B ● points-of-a-type (pr₁ B)
Sphere-UMP (succ n) B = (Susp⊣Ω.equiv (Sphere⊙ n) B) ● Sphere-UMP n (Ω B)




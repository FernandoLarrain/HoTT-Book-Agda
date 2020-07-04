{-# OPTIONS --without-K --exact-split --rewriting #-}

open import Ch1.Type-theory
open import Ch2.Homotopy-type-theory
open import Ch3.Sets-and-logic

module Ch6.2-Induction-pples-and-dependent-paths where


-- Equation 6.2.2 (New notation for the type of dependent paths between two points, a.k.a. "PathOvers").

{- Note: up to this point in the book, no official definition of PathOver was required; transport and _≡_ sufficed. -} 

PathOver : {X : 𝓤 ̇} (P : X → 𝓥 ̇) {x y : X} (p : x ≡ y) (u : P x) (v : P y) → 𝓥 ̇
PathOver P p u v = transport P p u ≡ v

infix 0 PathOver

syntax PathOver P p u v = u ≡ v [ P ↓ p ]

module PathOver'-1-is-PathOver where

  open higher-paths

  BndryOver-agreement : {X : 𝓤 ̇} (P : X → 𝓥 ̇) (b : Bndry 1 X) → BndryOver 1 P b ≡ P (lhs b) × P (rhs b)
  BndryOver-agreement P b = ua (BndryOver 1 P b) (P (lhs b) × P (rhs b)) (pr₂ , qinv-to-isequiv ((lift ⋆ ,_) , (refl , β)))
    where
    β :  (lift ⋆ ,_) ∘ pr₂ ∼ id
    β (lift ⋆ , w) = dpair-≡ ((refl _) , (refl _))

  BndryOver-agreement' : {X : 𝓤 ̇} (P : X → 𝓥 ̇) (b : Bndry 1 X) → BndryOver 1 P b ≃ P (lhs b) × P (rhs b)
  BndryOver-agreement' P b = (pr₂ , qinv-to-isequiv ((lift ⋆ ,_) , (refl , β)))
    where
    β :  (lift ⋆ ,_) ∘ pr₂ ∼ id
    β (lift ⋆ , w) = dpair-≡ ((refl _) , (refl _))

  {- Alternatively, use Σ-over-Contr-base-is-fib -}

  PathOver-agreement : {X : 𝓤 ̇} (P : X → 𝓥 ̇) {b : Bndry 1 X} (p : Path 1 b) (b' : BndryOver 1 P b) → PathOver' 1 P {b} p b' ≡ PathOver P p (pr₁ (pr₂ b')) (pr₂ (pr₂ b')) 
  PathOver-agreement P (refl _) b' = refl _

  PathOver-agreement' : {X : 𝓤 ̇} (P : X → 𝓥 ̇) {b : Bndry 1 X} (p : Path 1 b) (b' : BndryOver 1 P b) → PathOver' 1 P {b} p b' ≃ PathOver P p (pr₁ (pr₂ b')) (pr₂ (pr₂ b')) 
  PathOver-agreement' P p b' = idtoeqv _ _ (PathOver-agreement P p b')
  

-- The rewrite relation _↦_.

{- Agda has no native support for HITs, so we have to postulate them. To obtain definitonal equality for point constructors, we extend Agda's evaluation relation with new computation rules defined via _↦_ -}

postulate

  _↦_ : {A : 𝓤 ̇} → A → A → 𝓤 ̇

infix 0 _↦_

{-# BUILTIN REWRITE _↦_ #-} 


-- The Circle, 𝕊¹.

postulate

  -- (i) Type formation rule

  𝕊¹ : 𝓤₀ ̇

  -- (ii) Constructors
  
  base₁ : 𝕊¹ -- point constructor
  loop₁ : base₁ ≡ base₁ -- path constructor

module _ (P : 𝕊¹ → 𝓤 ̇) (b : P base₁) (l : b ≡ b [ P ↓ loop₁ ]) where

  postulate

    -- (iii) Induction principle

    𝕊¹-ind : Π P
  
    -- (iv) Computation rules

    base₁-β : 𝕊¹-ind base₁ ↦ b

    {-# REWRITE base₁-β #-}

    loop₁-β : apd 𝕊¹-ind loop₁ ≡ l


-- Lemma 6.2.5 (Recursion principle for 𝕊¹).

module _ {A : 𝓤 ̇} (a : A) (p : a ≡ a) where

  -- (v) Recursion principle
  
  𝕊¹-rec : 𝕊¹ → A
  𝕊¹-rec = 𝕊¹-ind (λ x → A)  a (transportconst A loop₁ a ∙ p)

  -- (vi) Computation rules

  base₁-β' : 𝕊¹-rec base₁ ≡ a
  base₁-β' = refl _

  loop₁-β' : ap 𝕊¹-rec loop₁ ≡ p
  loop₁-β' = ∙ₗ-inv _ (ap 𝕊¹-rec loop₁) p (apd-const A 𝕊¹-rec loop₁ ⁻¹ ∙ loop₁-β (λ x → A) a (transportconst A loop₁ a ∙ p))
  

-- Lemma 6.2.8 (Uniqueness principle for 𝕊¹)

𝕊¹-η' : {A : 𝓤 ̇} (f g : 𝕊¹ → A) (p : f base₁ ≡ g base₁) (q : ap f loop₁ ≡ ap g loop₁ [ (λ - → - ≡ -) ↓ p ]) → f ∼ g
𝕊¹-η' {A = A} f g p q = 𝕊¹-ind (λ x → f x ≡ g x) p (
  transport-funval-≡ f g loop₁ p ∙
  ap (λ - → ap f loop₁ ⁻¹ ∙ p ∙ -) (q ⁻¹ ∙  transport-loop p (ap f loop₁)) ∙
  ∙-assoc _ _ _ ⁻¹ ∙
  ap (ap f loop₁ ⁻¹ ∙_) (∙-assoc _ _ _) ∙
  ap (λ - → ap f loop₁ ⁻¹ ∙ (- ∙ p)) (∙-assoc _ _ _) ∙
  ap (λ - → ap f loop₁ ⁻¹ ∙ (- ∙ p)) (ap (_∙ ap f loop₁) (rinv _) ∙ (lu _ ⁻¹)) ∙    ∙-assoc _ _ _ ∙
  ap (_∙ p) (linv _) ∙
  lu _ ⁻¹
  )


-- Lemma 6.2.9 (UMP of 𝕊¹).

UMP-𝕊¹ : (A : 𝓤 ̇) → (𝕊¹ → A) ≃ (Σ x ꞉ A , x ≡ x)
UMP-𝕊¹ A =
  (λ f → (f base₁ , ap f loop₁)) ,
  (qinv-to-isequiv (
    Σ-induction (𝕊¹-rec {A = A}) ,
    Σ-induction (λ a l → dpair-≡ (refl _ , loop₁-β' a l)) ,
    λ f → funext _ _ (𝕊¹-η' _ _ (refl _) (loop₁-β' (f base₁) (ap f loop₁))) 
    )
  )


    

  


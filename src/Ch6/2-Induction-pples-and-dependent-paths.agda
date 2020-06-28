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
  
  base¹ : 𝕊¹ -- point constructor
  loop : base¹ ≡ base¹ -- path constructor

module _ (P : 𝕊¹ → 𝓤 ̇) (b : P base¹) (l : b ≡ b [ P ↓ loop ]) where

  postulate

    -- (iii) Induction principle

    𝕊¹-ind : Π P
  
    -- (iv) Computation rules

    base¹-β : 𝕊¹-ind base¹ ↦ b

    {-# REWRITE base¹-β #-}

    loop-β : apd 𝕊¹-ind loop ≡ l


-- Lemma 6.2.5 (Recursion principle for 𝕊¹).

module _ {A : 𝓤 ̇} (a : A) (p : a ≡ a) where

  𝕊¹-rec : 𝕊¹ → A
  𝕊¹-rec = 𝕊¹-ind (λ x → A)  a (transportconst A loop a ∙ p)
  
  base¹-β' : 𝕊¹-rec base¹ ≡ a
  base¹-β' = refl _

  loop-β' : ap 𝕊¹-rec loop ≡ p
  loop-β' = ∙ₗ-inv _ (ap 𝕊¹-rec loop) p (apd-const A 𝕊¹-rec loop ⁻¹ ∙ loop-β (λ x → A) a (transportconst A loop a ∙ p))
  

-- Lemma 6.2.8 (Uniqueness principle for 𝕊¹)

𝕊¹-η' : {A : 𝓤 ̇} (f g : 𝕊¹ → A) (p : f base¹ ≡ g base¹) (q : ap f loop ≡ ap g loop [ (λ - → - ≡ -) ↓ p ]) → f ∼ g
𝕊¹-η' {A = A} f g p q = 𝕊¹-ind (λ x → f x ≡ g x) p (
  transport-funval-≡ f g loop p ∙
  ap (λ - → ap f loop ⁻¹ ∙ p ∙ -) (q ⁻¹ ∙  transport-loop p (ap f loop)) ∙
  ∙-assoc _ _ _ ⁻¹ ∙
  ap (ap f loop ⁻¹ ∙_) (∙-assoc _ _ _) ∙
  ap (λ - → ap f loop ⁻¹ ∙ (- ∙ p)) (∙-assoc _ _ _) ∙
  ap (λ - → ap f loop ⁻¹ ∙ (- ∙ p)) (ap (_∙ ap f loop) (rinv _) ∙ (lu _ ⁻¹)) ∙    ∙-assoc _ _ _ ∙
  ap (_∙ p) (linv _) ∙
  lu _ ⁻¹
  )


-- Lemma 6.2.9 (UMP of 𝕊¹).

UMP-𝕊¹ : (A : 𝓤 ̇) → (𝕊¹ → A) ≃ (Σ x ꞉ A , x ≡ x)
UMP-𝕊¹ A =
  (λ f → (f base¹ , ap f loop)) ,
  (qinv-to-isequiv (
    Σ-induction (𝕊¹-rec {A = A}) ,
    Σ-induction (λ a l → dpair-≡ (refl _ , loop-β' a l)) ,
    λ f → funext _ _ (𝕊¹-η' _ _ (refl _) (loop-β' (f base¹) (ap f loop))) 
    )
  )


    

  


{-# OPTIONS --without-K --exact-split --rewriting #-}

open import Ch1.Type-theory
open import Ch2.Homotopy-type-theory
open import Ch3.Sets-and-logic
open import Ch6.2-Induction-pples-and-dependent-paths

module Ch6.3-The-interval where


-- The interval, I.

postulate

  -- (i) Type formation rule

  I : 𝓤₀ ̇

  -- (ii) Constructors
  
  i0 : I -- Cubical Agda notation
  i1 : I
  seg : i0 ≡ i1 

module _ (P : I → 𝓤 ̇) (b₀ : P i0) (b₁ : P i1) (s : b₀ ≡ b₁ [ P ↓ seg ]) where

  postulate

    -- (iii) Induction principle

    I-ind : Π P
  
    -- (iv) Computation rules

    i0-β : I-ind i0 ↦ b₀

    {-# REWRITE i0-β #-}

    i1-β : I-ind i1 ↦ b₁

    {-# REWRITE i1-β #-}
    
    seg-β : apd I-ind seg ≡ s


-- Recursion principle for I

module _ {B : 𝓤 ̇} (b₀ b₁ : B) (s : b₀ ≡ b₁) where

  I-rec : I → B
  I-rec = I-ind (λ i → B) b₀ b₁ (transportconst B seg b₀ ∙ s)

  i0-β' : I-rec i0 ≡ b₀
  i0-β' = refl _

  i1-β' : I-rec i1 ≡ b₁
  i1-β' = refl _

  seg-β' : ap I-rec seg ≡ s
  seg-β' = ∙ₗ-inv _ (ap I-rec seg) s (apd-const B I-rec seg ⁻¹ ∙ seg-β (λ i → B) b₀ b₁ (transportconst B seg b₀ ∙ s))


-- Lemma 6.3.1 (I is contractible).

I-is-Contr : isContr I
I-is-Contr = i0 , I-ind (λ i → i0 ≡ i) (refl _) seg (transport-post-∙ I i0 _ _ seg (refl i0) ∙ lu _ ⁻¹)


-- Lemma 6.3.2 (Function Extensionality)

I-implies-funext : {A : 𝓤 ̇} {B : 𝓥 ̇} (f g : A → B) → f ∼ g → f ≡ g
I-implies-funext {A = A} {B} f g p = ap q seg
  where
  p' : A → I → B
  p' x = I-rec (f x) (g x) (p x)
  q : I → A → B
  q i = λ x → p' x i 

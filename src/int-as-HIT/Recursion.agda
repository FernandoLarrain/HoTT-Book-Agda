{-# OPTIONS --without-K --exact-split --rewriting #-}

open import Ch1.Type-theory
open import Ch2.Homotopy-type-theory
open import Ch3.Sets-and-logic
open import Rewrite
open import Ch6.4-Circles-and-spheres-safe

module int-as-HIT.Recursion where


-- Definition 1 (Integers as signed natural numbers).

data ℤω : 𝓤₀ ̇ where
  0ω : ℤω
  strpos : ℕ → ℤω
  strneg : ℕ → ℤω
  

-- Definition 2 (Integers as HIT).

postulate

  -- (i) Type formation rule

  ℤₕ : 𝓤₀ ̇

  -- (ii) Introduction rules

  0ₕ : ℤₕ
  succₕ : ℤₕ → ℤₕ
  predₕ : ℤₕ → ℤₕ
  secₕ : predₕ ∘ succₕ ∼ id
  retₕ : succₕ ∘ predₕ ∼ id
  cohₕ : (z : ℤₕ) → ap succₕ (secₕ z) ≡ retₕ (succₕ z)

module _ (B : 𝓤 ̇) (b₀ : B) (succ' : B → B) (pred' : B → B) (sec' : pred' ∘ succ' ∼ id) (ret' : succ' ∘ pred' ∼ id) (coh' : (b : B) → ap succ' (sec' b) ≡ ret' (succ' b)) where

  postulate

    -- (iii) Recursion principle

    ℤₕ-rec : ℤₕ → B

    -- (iv) Computation rules

    0-β : ℤₕ-rec 0ₕ ↦ b₀
    
    {-# REWRITE 0-β #-}

    succ-β : (z : ℤₕ) → ℤₕ-rec (succₕ z) ↦ succ' (ℤₕ-rec z)
    
    {-# REWRITE succ-β #-} 

    pred-β : (z : ℤₕ) → ℤₕ-rec (predₕ z) ↦ pred' (ℤₕ-rec z)

    {-# REWRITE pred-β #-}    

    sec-β : (z : ℤₕ) → ap ℤₕ-rec (secₕ z) ≡ sec' (ℤₕ-rec z)

    ret-β : (z : ℤₕ) → ap ℤₕ-rec (retₕ z) ≡ ret' (ℤₕ-rec z)

    coh-β : (z : ℤₕ) → ap² ℤₕ-rec (cohₕ z) ≡
      (ap-∘ succₕ ℤₕ-rec (secₕ z) ∙ (ru _ ∙ hnat (hrefl _) (secₕ z) ⁻¹ ∙ lu _ ⁻¹) ∙ ap-∘ ℤₕ-rec succ' (secₕ z) ⁻¹) ∙ ap (ap succ') (sec-β z) ∙ coh' (ℤₕ-rec z) ∙ ret-β (succₕ z) ⁻¹ -- check that it agrees with the definition of homomorphism

  module _ (g : ℤₕ → B) (p : g 0ₕ ≡ b₀) (α : g ∘ succₕ ∼ succ' ∘ g) where  

    postulate

      -- (v) Uniqueness principle
    
      ℤₕ-η : ℤₕ-rec ∼ g
      
      -- (vi) βη-coherence

      0-βη : ℤₕ-η 0ₕ ∙ p ≡ refl b₀

      succ-βη : (z : ℤₕ) → ℤₕ-η (succₕ z) ∙ α z ≡ ap succ' (ℤₕ-η z)


-- Theorem : ℤω ≃ ℤₕ

-- 1. Embedding ℤω into ℤₕ

strposₕ : ℕ → ℤₕ
strposₕ 0 = succₕ 0ₕ
strposₕ (succ n) = succₕ (strposₕ n)

strnegₕ : ℕ → ℤₕ
strnegₕ 0 = predₕ 0ₕ
strnegₕ (succ n) = predₕ (strnegₕ n)

embedding : ℤω → ℤₕ
embedding 0ω = 0ₕ
embedding (strpos n) = strposₕ n
embedding (strneg n) = strnegₕ n

-- 2. Normalizing terms in ℤₕ

succω : ℤω → ℤω
succω 0ω = strpos 0
succω (strpos n) = strpos (succ n)
succω (strneg 0) = 0ω
succω (strneg (succ n)) = strneg n

predω : ℤω → ℤω
predω 0ω = strneg 0
predω (strpos 0) = 0ω
predω (strpos (succ n)) = strpos n
predω (strneg n) = strneg (succ n)

secω : (z : ℤω) → predω (succω z) ≡ z
secω 0ω = refl _
secω (strpos n) = refl _
secω (strneg 0) = refl _
secω (strneg (succ n)) = refl _

retω : (z : ℤω) → succω (predω z) ≡ z
retω 0ω = refl _
retω (strpos 0) = refl _
retω (strpos (succ n)) = refl _
retω (strneg n) = refl _

cohω : (z : ℤω) → ap succω (secω z) ≡ retω (succω z)
cohω 0ω = refl _
cohω (strpos n) = refl _
cohω (strneg 0) = refl _
cohω (strneg (succ n)) = refl _

normalization : ℤₕ → ℤω
normalization = ℤₕ-rec _ 0ω succω predω secω retω cohω

-- 3. Embedding is section of normalization

norm-has-sec : normalization ∘ embedding ∼ id
norm-has-sec 0ω = refl _
norm-has-sec (strpos 0) = refl _
norm-has-sec (strpos (succ n)) = ap succω (norm-has-sec (strpos n))
norm-has-sec (strneg 0) = refl _
norm-has-sec (strneg (succ n)) = ap predω (norm-has-sec (strneg n))

-- 4. Normalization is section of embedding

rec-id : ℤₕ-rec ℤₕ 0ₕ succₕ predₕ secₕ retₕ cohₕ ∼ id
rec-id = ℤₕ-η ℤₕ 0ₕ succₕ predₕ secₕ retₕ cohₕ id (refl _) (hrefl _)

rec-emb∘norm : ℤₕ-rec ℤₕ 0ₕ succₕ predₕ secₕ retₕ cohₕ ∼ embedding ∘ normalization
rec-emb∘norm = ℤₕ-η ℤₕ 0ₕ succₕ predₕ secₕ retₕ cohₕ (embedding ∘ normalization) (refl _) (λ z → embedding (normalization (succₕ z)) ≡⟨ refl _ ⟩ embedding (succω (normalization z)) ≡⟨ aux (normalization z) ⟩ succₕ (embedding (normalization z)) ∎) where
  aux : embedding ∘ succω ∼ succₕ ∘ embedding
  aux 0ω = refl _
  aux (strpos x) = refl _
  aux (strneg zero) = retₕ 0ₕ ⁻¹
  aux (strneg (succ x)) = retₕ (strnegₕ x) ⁻¹

emb-has-sec : embedding ∘ normalization ∼ id
emb-has-sec z = rec-emb∘norm z ⁻¹ ∙ rec-id z

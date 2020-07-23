{-# OPTIONS --without-K --exact-split --rewriting #-}

open import Ch1.Type-theory
open import Ch2.Homotopy-type-theory
open import Ch3.Sets-and-logic
open import Ch6.2-Induction-pples-and-dependent-paths
open import Ch6.4-Circles-and-spheres

module int-as-HIT.replica where

-- Definition 1 (Integers as signed natural numbers).

data ℤω : 𝓤₀ ̇ where
  0ω : ℤω
  strpos : ℕ → ℤω
  strneg : ℕ → ℤω


-- Definition 2 (Integers as HIT)

-- The following function is useful for expressing the induction principle of ℤₕ:

ap-over : {A : 𝓤 ̇} {P : A → 𝓥 ̇} {Q : A → 𝓦 ̇} (f : (x : A) → P x → Q x) {x y : A} (p : x ≡ y) {u : P x} {v : P y} → u ≡ v [ P ↓ p ] → f x u ≡ f y v [ Q ↓ p ]
ap-over f (refl x) h = ap (f x) h

ap-over' : {A : 𝓤 ̇} {P : A → 𝓥 ̇} {Q : A → 𝓦 ̇} (f : (x : A) → P x → Q x) {x y : A} (p : x ≡ y) {u : P x} {v : P y} → u ≡ v [ P ↓ p ] → f x u ≡ f y v [ Q ↓ p ]
ap-over' {P = P} {Q} f {x} {y} p {u} h = transport-fun-family P Q f _ _ p u ∙ ap (f y) h

ap-over-agreement : {A : 𝓤 ̇} {P : A → 𝓥 ̇} {Q : A → 𝓦 ̇} (f : (x : A) → P x → Q x) {x y : A} (p : x ≡ y) {u : P x} {v : P y} (h : u ≡ v [ P ↓ p ]) → ap-over f p h ≡ ap-over f p h
ap-over-agreement f (refl x) (refl u) = refl _

postulate

  -- (i) Type formation rule

  ℤₕ : 𝓤₀ ̇

  -- (ii) Introduction rules

  0ₕ : ℤₕ

  succₕ : ℤₕ → ℤₕ

  predₕ : ℤₕ → ℤₕ

  secₕ : (z : ℤₕ) → predₕ (succₕ z) ≡ z

  retₕ : (z : ℤₕ) → succₕ (predₕ z) ≡ z

  cohₕ : (z : ℤₕ) → ap succₕ (secₕ z) ≡ retₕ (succₕ z)

module _

  (B : 𝓤 ̇)

  (b₀ : B)

  (next : B → B)

  (previous : B → B)

  (σ : (b : B) → previous (next b) ≡ b)

  (ρ : (b : B) → next (previous b) ≡ b)

  (τ : (b : B) → ap next (σ b) ≡  ρ (next b))

  where

  postulate

    -- (iii) Recursion principle

    ℤₕ-rec : ℤₕ → B

    -- (iv) Computation rules

    0ₕ-β : ℤₕ-rec 0ₕ ↦ b₀

    {-# REWRITE 0ₕ-β #-}

    succₕ-β : (z : ℤₕ) → ℤₕ-rec (succₕ z) ↦ next (ℤₕ-rec z)

    {-# REWRITE succₕ-β #-} 

    predₕ-β : (z : ℤₕ) → ℤₕ-rec (predₕ z) ↦ previous (ℤₕ-rec z)

    {-# REWRITE predₕ-β #-}    

    secₕ-β : (z : ℤₕ) → ap ℤₕ-rec (secₕ z) ≡ σ (ℤₕ-rec z)

    retₕ-β : (z : ℤₕ) → ap ℤₕ-rec (retₕ z) ≡ ρ (ℤₕ-rec z)

    cohₕ-β : (z : ℤₕ) → ap² ℤₕ-rec (cohₕ z) ≡ ap-∘ succₕ ℤₕ-rec (secₕ z) ∙ ap-∘ ℤₕ-rec next (secₕ z) ⁻¹ ∙ ap² next (secₕ-β z) ∙ τ (ℤₕ-rec z) ∙ retₕ-β (succₕ z) ⁻¹

module _

  (P : ℤₕ → 𝓤 ̇)

  (u₀ : P 0ₕ)

  (next : (z : ℤₕ) → P z → P (succₕ z))

  (previous : (z : ℤₕ) → P z → P (predₕ z))

  (σ : (z : ℤₕ) (u : P z) → previous (succₕ z) (next z u) ≡ u [ P ↓ secₕ z ])

  (ρ : (z : ℤₕ) (u : P z) → next (predₕ z) (previous z u) ≡ u [ P ↓ retₕ z ])

  (τ : ( z : ℤₕ) (u : P z) → transport-∘ P succₕ (secₕ z) _ ⁻¹ ∙  ap-over next (secₕ z) (σ z u) ≡ ρ (succₕ z) (next z u) [ P ⇊ cohₕ z ])

  where

  postulate

    -- (v) Induction Principle

    ℤₕ-ind : (z : ℤₕ) → P z

    -- (vi) Computation rules

    0ₕ-β' : ℤₕ-ind 0ₕ ↦ u₀

    {-# REWRITE 0ₕ-β' #-}

    succₕ-β' : (z : ℤₕ) → ℤₕ-ind (succₕ z) ↦ next z (ℤₕ-ind z)

    {-# REWRITE succₕ-β' #-} 

    predₕ-β' : (z : ℤₕ) → ℤₕ-ind (predₕ z) ↦ previous z (ℤₕ-ind z)

    {-# REWRITE predₕ-β' #-}    

    secₕ-β' : (z : ℤₕ) → apd ℤₕ-ind (secₕ z) ≡ σ z (ℤₕ-ind z)

    retₕ-β' : (z : ℤₕ) → apd ℤₕ-ind (retₕ z) ≡ ρ z (ℤₕ-ind z)

--    cohₕ-β' : (z : ℤₕ) → apd² ℤₕ-ind (cohₕ z) ≡ {!!} ∙ τ z (ℤₕ-ind z) ∙ (transport² P (cohₕ z) _ ∙ₗ {!!}) -- dependent 1-paths can be directly equated because dependent 0-paths are just applications of the dependent function, but dependent 2-paths can in general only be equated via a dependent 1-path, so this rule should be a PathOver rather than a regular path. We might also want to use ``hubs and spokes'' instead.

-- shouldn't computation rules for dependent functions be phrased in terms of dependent paths?
    

-- Theorem: ℤω ≃ ℤₕ


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

-- CHECK INDUCTION PRINCIPLE OF ℤₕ 

emb-has-sec : embedding ∘ normalization ∼ id
emb-has-sec = ℤₕ-ind (λ z → embedding (normalization z) ≡ z) (refl _) {!!} {!!} {!!} {!!} {!!}

-- Check definition of integers

-- Alternative definitions:

-- Free grp on one generator

-- Contractible fibers

-- Loop space of circle

-- Signed nats

-- Successor with contractible fibers

-- Successor with bi-invertible maps

-- Induction pple as recursion + eta

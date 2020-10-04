{-# OPTIONS --without-K --exact-split --rewriting #-}

open import Ch1.Type-theory
open import Ch2.Homotopy-type-theory
open import Ch3.Sets-and-logic
open import Ch4.Equivalences
open import Rewrite
-- open import Ch6.4-Circles-and-spheres-safe

module int-as-HIT.replica where


-- Definition 1.1 (Integers as signed natural numbers).

data ℤω : 𝓤₀ ̇ where
  0ω : ℤω
  strpos : ℕ → ℤω
  strneg : ℕ → ℤω
  

-- Defining 2-paths as iterated 1-paths

PathOver² : {A : 𝓤 ̇} (P : A → 𝓥 ̇) {x y : A} {p q : x ≡ y} (r : p ≡ q) {u : P x} {v : P y} (h : u ≡ v [ P ↓ p ]) (k : u ≡ v [ P ↓ q ]) → 𝓥 ̇
PathOver² P {x} {y} r {u} {v} h k = h ≡ k [ (λ (- : x ≡ y) → u ≡ v [ P ↓ - ]) ↓ r ]

infix 0 PathOver²

syntax PathOver² P r h k = h ≡ k [ P ⇊ r ]


apd² : {A : 𝓤 ̇} {P : A → 𝓥 ̇} {x y : A} {p q : x ≡ y} (f : (x : A) → P x) (r : p ≡ q) → apd f p ≡ apd f q [ P ⇊ r ]
apd² f (refl (refl x)) = refl (refl (f x))


ap-over : {X : 𝓤 ̇} {Y : 𝓥 ̇} (P : X → 𝓦 ̇) (Q : Y → 𝓣 ̇) (f : X → Y) (g : (x : X) → P x → Q (f x)) {x₁ x₂ : X} (p : x₁ ≡ x₂) {u₁ : P x₁} {u₂ : P x₂} → u₁ ≡ u₂ [ P ↓ p ] → g x₁ u₁ ≡ g x₂ u₂ [ Q ↓ ap f p ]
ap-over P Q f g (refl _) q = ap (g _) q


ap-over-nat : {X : 𝓤 ̇} {Y : 𝓥 ̇} (P : X → 𝓦 ̇) (Q : Y → 𝓣 ̇) (f : X → Y) (g : (x : X) → P x → Q (f x)) (h : (x : X) → P x) (k : (y : Y) → Q y) (α : (x : X) → g x (h x) ≡ k (f x)) {x₁ x₂ : X} (p : x₁ ≡ x₂) → ap-over P Q f g p (apd h p) ≡ ap (transport Q (ap f p)) (α x₁) ∙ apd k (ap f p) ∙ α x₂ ⁻¹   
ap-over-nat P Q f g h k α {x₁} (refl _) = rinv _ ⁻¹ ∙ ((ap-id (α x₁) ⁻¹ ∙ ru (ap id (α x₁))) ∙ᵣ α x₁ ⁻¹)

apd-∘ : {X : 𝓤 ̇} {Y : 𝓥 ̇} {Q : Y → 𝓦 ̇} (f : X → Y) (g : (y : Y) → Q y) {x₁ x₂ : X} (p : x₁ ≡ x₂) → apd g (ap f p) ≡ transport-∘ Q f p (g (f x₁)) ⁻¹ ∙ apd (g ∘ f) p
apd-∘ f g (refl _) = refl _


-- Definition 1.2 (Integers using hae's).

postulate

  -- (i) Type formation
  
  ℤₕ : 𝓤₀ ̇

  -- (ii) Constructors
  
  0ₕ : ℤₕ
  succₕ : ℤₕ → ℤₕ
  predₕ : ℤₕ → ℤₕ
  secₕ : predₕ ∘ succₕ ∼ id
  retₕ : succₕ ∘ predₕ ∼ id
  cohₕ : (z : ℤₕ) → ap succₕ (secₕ z) ≡ retₕ (succₕ z)

module _ {𝓤 : Universe} (P : ℤₕ → 𝓤 ̇) (0ₚ : P 0ₕ) (succₚ : (z : ℤₕ) → P z → P (succₕ z)) (predₚ : (z : ℤₕ) → P z → P (predₕ z)) (secₚ : (z : ℤₕ) (u : P z) → predₚ (succₕ z) (succₚ z u) ≡ u [ P ↓ secₕ z ]) (retₚ : (z : ℤₕ) (u : P z) → succₚ (predₕ z) (predₚ z u) ≡ u [ P ↓ retₕ z ]) (cohₚ : (z : ℤₕ) (u : P z) → ap-over P P succₕ succₚ (secₕ z) (secₚ z u) ≡ retₚ (succₕ z) (succₚ z u) [ P ⇊ cohₕ z ]) where

  postulate

    -- (iii) Eliminator

    ℤₕ-ind : (z : ℤₕ) → P z

    -- (iv) Computation rules

    succ-β : (z : ℤₕ) → ℤₕ-ind (succₕ z) ↦ succₚ z (ℤₕ-ind z)
    
    {-# REWRITE succ-β #-}

    pred-β : (z : ℤₕ) → ℤₕ-ind (predₕ z) ↦ predₚ z (ℤₕ-ind z)

    {-# REWRITE pred-β #-}

    sec-β : (z : ℤₕ) → apd ℤₕ-ind (secₕ z) ≡ secₚ z (ℤₕ-ind z)

    ret-β : (z : ℤₕ) → apd ℤₕ-ind (retₕ z) ≡ retₚ z (ℤₕ-ind z)

  nat-lemma : {z₁ z₂ : ℤₕ} (p : z₁ ≡ z₂) → apd ℤₕ-ind (ap succₕ p) ≡ ap-over P P succₕ succₚ p (apd ℤₕ-ind p) -- particular case of ap-over-nat
  nat-lemma (refl _) = refl _

  postulate

    coh-β : (z : ℤₕ) → apd² ℤₕ-ind (cohₕ z) ≡
      ap (transport (λ - → succₚ (predₕ (succₕ z)) (predₚ (succₕ z) (succₚ z (ℤₕ-ind z))) ≡ succₚ z (ℤₕ-ind z) [ P ↓ - ]) (cohₕ z)) (nat-lemma (secₕ z) ∙ ap (ap-over P P succₕ succₚ (secₕ z)) (sec-β z)) ∙ cohₚ z (ℤₕ-ind z) ∙ (ret-β (succₕ z)) ⁻¹


-- -- Recursion principle for ℤₕ

-- ℤₕ-rec : (B : 𝓤 ̇) (b₀ : B) (succ' : B → B) (pred' : B → B) (sec' : pred' ∘ succ' ∼ id) (ret' : succ' ∘ pred' ∼ id) (coh' : (b : B) → ap succ' (sec' b) ≡ ret' (succ' b)) → ℤₕ → B
-- ℤₕ-rec B b₀ succ' pred' sec' ret' coh' = ℤₕ-ind (λ z → B) b₀ (λ z → succ') (λ z → pred') (λ z b → transportconst B (secₕ z) (pred' (succ' b)) ∙ sec' b) (λ z b → transportconst B (retₕ z) (succ' (pred' b)) ∙ ret' b) λ z b → {!!}


module _ (B : 𝓤 ̇) (b₀ : B) (succ' : B → B) (pred' : B → B) (sec' : pred' ∘ succ' ∼ id) (ret' : succ' ∘ pred' ∼ id) (coh' : (b : B) → ap succ' (sec' b) ≡ ret' (succ' b)) where

  postulate

    -- (iii) Recursion principle

    ℤₕ-rec : ℤₕ → B

    -- (iv) Computation rules

    0-β' : ℤₕ-rec 0ₕ ↦ b₀
    
    {-# REWRITE 0-β' #-}

    succ-β' : (z : ℤₕ) → ℤₕ-rec (succₕ z) ↦ succ' (ℤₕ-rec z)
    
    {-# REWRITE succ-β' #-} 

    pred-β' : (z : ℤₕ) → ℤₕ-rec (predₕ z) ↦ pred' (ℤₕ-rec z)

    {-# REWRITE pred-β' #-}    

    sec-β' : (z : ℤₕ) → ap ℤₕ-rec (secₕ z) ≡ sec' (ℤₕ-rec z)

    ret-β' : (z : ℤₕ) → ap ℤₕ-rec (retₕ z) ≡ ret' (ℤₕ-rec z)

    coh-β' : (z : ℤₕ) → ap (ap ℤₕ-rec) (cohₕ z) ≡
      (ap-∘ succₕ ℤₕ-rec (secₕ z) ∙ (ru _ ∙ hnat (hrefl _) (secₕ z) ⁻¹ ∙ lu _ ⁻¹) ∙ ap-∘ ℤₕ-rec succ' (secₕ z) ⁻¹) ∙ ap (ap succ') (sec-β' z) ∙ coh' (ℤₕ-rec z) ∙ ret-β' (succₕ z) ⁻¹ -- check that it agrees with the definition of homomorphism


-- Uniqueness principle

uniqueness : (B : 𝓤 ̇) (b₀ : B) (succ' : B → B) (pred' : B → B) (sec' : pred' ∘ succ' ∼ id) (ret' : succ' ∘ pred' ∼ id) (coh' : (b : B) → ap succ' (sec' b) ≡ ret' (succ' b)) (f : ℤₕ → B) (p : f 0ₕ ≡ b₀) (α : f ∘ succₕ ∼ succ' ∘ f) (β : f ∘ predₕ ∼ pred' ∘ f) (γ : (z : ℤₕ) → ap f (secₕ z) ≡ β (succₕ z) ∙ ap pred' (α z) ∙ sec' (f z)) (δ : (z : ℤₕ) → ap f (retₕ z) ≡ α (predₕ z) ∙ ap succ' (β z) ∙ ret' (f z)) → f ∼ ℤₕ-rec B b₀ succ' pred' sec' ret' coh' --coherence is missing
uniqueness B b₀ succ' pred' sec' ret' coh' f p α β γ δ = ℤₕ-ind
  (λ z → f z ≡ rec z)
  p
  (λ z ih → α z ∙ ap succ' ih)
  (λ z ih → β z ∙ ap pred' ih)
  (λ z q → transport-funval-≡ f rec (secₕ z) (β (succₕ z) ∙ ap pred' (α z ∙ ap succ' q)) ∙ {!!}) -- doable
  {!!} -- symmetric to previous goal
  {!!} -- AAAAAAAAAAAAAAAA!!!!!
  where
  rec : ℤₕ → B
  rec = ℤₕ-rec B b₀ succ' pred' sec' ret' coh'

-- (B : 𝓤 ̇) (b₀ : B) (succ' : B → B) (pred' : B → B) (sec' : pred' ∘ succ' ∼ id) (ret' : succ' ∘ pred' ∼ id) (coh' : (b : B) → ap succ' (sec' b) ≡ ret' (succ' b)) (f : ℤₕ → B) (p : f 0 = b₀) (α : f ∘ succₕ ∼ succ' ∘ f) (β : f ∘ predₕ ∼ pred' ∘ f) (γ : (z : ℤₕ) → ap f (secₕ z) ≡ ?) (δ : (z : ℤₕ) → ap f (retₕ z) ≡ ?) → f ∼ recₕ B b₀ succ' pred' sec' ret' coh'


-- -- -- Normalization map

-- -- succω : ℤω → ℤω
-- -- succω 0ω = strpos zero
-- -- succω (strpos x) = strpos (succ x)
-- -- succω (strneg zero) = 0ω
-- -- succω (strneg (succ x)) = strneg x

-- -- predω : ℤω → ℤω
-- -- predω 0ω = strneg zero
-- -- predω (strpos zero) = 0ω
-- -- predω (strpos (succ x)) = strpos x
-- -- predω (strneg x) = strneg (succ x)

-- -- secω : predω ∘ succω ∼ id
-- -- secω 0ω = refl _
-- -- secω (strpos x) = refl _
-- -- secω (strneg zero) = refl _
-- -- secω (strneg (succ x)) = refl _

-- -- retω : succω ∘ predω ∼ id
-- -- retω 0ω = refl _
-- -- retω (strpos zero) = refl _
-- -- retω (strpos (succ x)) = refl _
-- -- retω (strneg x) = refl _

-- -- cohω : (z : ℤω) → ap succω (secω z) ≡ retω (succω z)
-- -- cohω 0ω = refl _
-- -- cohω (strpos x) = refl _
-- -- cohω (strneg zero) = refl _
-- -- cohω (strneg (succ x)) = refl _

-- -- -- norm : ℤₕ → ℤω
-- -- -- norm = ℤₕ-ind (λ - → ℤω) 0ω (λ z → succω) (λ z → predω) (λ z z' → transportconst ℤω (secₕ z) (predω (succω z')) ∙ secω z') (λ z z' → transportconst ℤω (retₕ z) (succω (predω z')) ∙ retω z') λ z z' → {!!}


-- -- -- -- Check definition of integers

-- -- -- -- Alternative definitions:

-- -- -- -- Free grp on one generator

-- -- -- -- Contractible fibers

-- -- -- -- Loop space of circle

-- -- -- -- Signed nats

-- -- -- -- Successor with contractible fibers

-- -- -- -- Successor with bi-invertible maps

-- -- -- -- Induction pple as recursion + eta

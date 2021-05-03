{-# OPTIONS --without-K --exact-split --rewriting #-}

open import Ch1.Type-theory
open import Ch2.Homotopy-type-theory
open import Ch3.Sets-and-logic
open import Ch4.Equivalences
open import Ch5.8-Id-types-and-id-systems
open import Thesis.Z-Algebras
open import Thesis.Identity-types
open import Thesis.Equivalence-preservation
open import Thesis.Hinitial-Z-Algebras
open import Thesis.Inductive-Z-Algebras
open import Thesis.Ind-iff-hinit
open import Rewrite

module Thesis.Z-as-HIT ⦃ fe : FunExt ⦄ where


-- I. The Integers as Signed Natural Numbers

data ℤω : 𝓤₀ ̇ where
  0ω : ℤω
  pos : ℕ → ℤω
  neg : ℕ → ℤω

-- ℤω is a ℤ-algebra

succω : ℤω → ℤω
succω 0ω = pos 0
succω (pos n) = pos (succ n)
succω (neg 0) = 0ω
succω (neg (succ n)) = neg n

predω : ℤω → ℤω
predω 0ω = neg 0
predω (pos 0) = 0ω
predω (pos (succ n)) = pos n
predω (neg n) = neg (succ n)

secω : (z : ℤω) → predω (succω z) ≡ z
secω 0ω = refl _
secω (pos n) = refl _
secω (neg 0) = refl _
secω (neg (succ n)) = refl _

retω : (z : ℤω) → succω (predω z) ≡ z
retω 0ω = refl _
retω (pos 0) = refl _
retω (pos (succ n)) = refl _
retω (neg n) = refl _

cohω : (z : ℤω) → ap succω (secω z) ≡ retω (succω z)
cohω 0ω = refl _
cohω (pos n) = refl _
cohω (neg 0) = refl _
cohω (neg (succ n)) = refl _

ℤω-≃ : ℤω ≃ ℤω
ℤω-≃ = (succω , predω , secω , retω , cohω)

ℤω-alg : Alg 𝓤₀
ℤω-alg = ℤω , 0ω , ℤω-≃


-- II. ℤω is initial

ℤω-has-rec : hasrec 𝓤 ℤω-alg
ℤω-has-rec (A , a₀ , s , p , σ , ρ , τ) = f , refl _ , f-s where
  f : ℤω → A
  f 0ω = a₀
  f (pos zero) = s a₀
  f (pos (succ n)) = s (f (pos n))
  f (neg zero) = p a₀
  f (neg (succ n)) = p (f (neg n))
  f-s : f ∘ succω ∼ s ∘ f
  f-s 0ω = refl (s a₀)
  f-s (pos n) = refl (s (f (pos n)))
  f-s (neg zero) = ρ a₀ ⁻¹
  f-s (neg (succ n)) = ρ (f (neg n)) ⁻¹ 

ℤω-has-rec-unique : (univ : Univalence) → hasrecunique 𝓤 ℤω-alg
ℤω-has-rec-unique {𝓤} univ (A , a₀ , s , p , σ , ρ , τ) (f , f₀ , f-s) (g , g₀ , g-s) = Hom-≡-intro ℤω-alg (A , a₀ , s , p , σ , ρ , τ) _ _ (H , H₀ , H-s)

  where

  f-i = pr₂ (fun-pres-to-hae-pres univ ℤω-≃ (s , p , σ , ρ , τ) f f f-s)
  f-p = pr₁ f-i
  f-σ = pr₁ (pr₂ f-i)
  f-ρ = pr₁ (pr₂ (pr₂ f-i))
  f-τ = pr₂ (pr₂ (pr₂ f-i))
  g-i = pr₂ (fun-pres-to-hae-pres univ ℤω-≃ (s , p , σ , ρ , τ) g g g-s)
  g-p = pr₁ g-i
  g-σ = pr₁ (pr₂ g-i)
  g-ρ = pr₁ (pr₂ (pr₂ g-i))
  g-τ = pr₂ (pr₂ (pr₂ g-i))
  H : f ∼ g
  H 0ω = f₀ ∙ g₀ ⁻¹
  H (pos zero) = f-s 0ω ∙ ap s (H 0ω) ∙ g-s 0ω ⁻¹
  H (pos (succ n)) = f-s (pos n) ∙ ap s (H (pos n)) ∙ g-s (pos n) ⁻¹
  H (neg zero) = f-p 0ω ∙ ap p (H 0ω) ∙ g-p 0ω ⁻¹
  H (neg (succ n)) = f-p (neg n) ∙ ap p (H (neg n)) ∙ g-p (neg n) ⁻¹
  H₀ : H 0ω ≡ f₀ ∙ g₀ ⁻¹
  H₀ = refl _
  aux1 : {a₁ a₂ a₃ a₄ x y : A} (p₁ : a₁ ≡ _) (p₂ : a₂ ≡ _) (p₃ : a₃ ≡ _) (p₄ : a₄ ≡ _) (q : x ≡ y) → (p₂ ∙ ap s p₁) ∙ ap (s ∘ p) q ∙ (p₄ ∙ ap s p₃) ⁻¹ ≡ p₂ ∙ ap s (p₁ ∙ ap p q ∙ p₃ ⁻¹) ∙ p₄ ⁻¹
  aux1 (refl _) (refl _) (refl _) (refl _) (refl _) = refl _
  H-s : (z : ℤω) → H (succω z) ≡ f-s z ∙ ap s (H z) ∙ g-s z ⁻¹
  H-s 0ω = refl (f-s 0ω ∙ ap s (H 0ω) ∙ g-s 0ω ⁻¹)
  H-s (pos n) = refl (f-s (pos n) ∙ ap s (H (pos n)) ∙ g-s (pos n) ⁻¹)
  H-s (neg zero) = ap-id (H 0ω) ⁻¹ ∙ hnat' ρ (H 0ω) ⁻¹ ∙ (aux2 ✦ refl _ ✦ aux3) ∙ aux1 _ _ _ _ _ where
    aux2 : ρ (f 0ω) ⁻¹ ≡ f-s (neg zero) ∙ ap s (f-p 0ω)
    aux2 = lu _ ∙ (f-ρ 0ω ∙ᵣ ρ (f 0ω) ⁻¹) ∙ ∙-assoc _ _ _ ⁻¹ ∙ (_ ∙ₗ rinv _) ∙ ru _ ⁻¹
    aux3 : ρ (g 0ω) ≡ (g-s (neg zero) ∙ ap s (g-p 0ω)) ⁻¹
    aux3 = ⁻¹-invol _ ⁻¹ ∙ ap _⁻¹ (lu _ ∙ (g-ρ 0ω ∙ᵣ ρ (g 0ω) ⁻¹) ∙ ∙-assoc _ _ _ ⁻¹ ∙ (_ ∙ₗ rinv _) ∙ ru _ ⁻¹)
  H-s (neg (succ n)) = ap-id (H (neg n)) ⁻¹ ∙ hnat' ρ (H (neg n)) ⁻¹ ∙ (aux2 ✦ refl _ ✦ aux3) ∙ aux1 _ _ _ _ _ where
    aux2 : ρ (f (neg n)) ⁻¹ ≡ f-s (neg (succ n)) ∙ ap s (f-p (neg n))
    aux2 = lu _ ∙ (f-ρ (neg n) ∙ᵣ ρ (f (neg n)) ⁻¹) ∙ ∙-assoc _ _ _ ⁻¹ ∙ (_ ∙ₗ rinv _) ∙ ru _ ⁻¹
    aux3 : ρ (g (neg n)) ≡ (g-s (neg (succ n)) ∙ ap s (g-p (neg n))) ⁻¹
    aux3 = ⁻¹-invol _ ⁻¹ ∙ ap _⁻¹ (lu _ ∙ (g-ρ (neg n) ∙ᵣ ρ (g (neg n)) ⁻¹) ∙ ∙-assoc _ _ _ ⁻¹ ∙ (_ ∙ₗ rinv _) ∙ ru _ ⁻¹)

ℤω-is-init : (univ : Univalence) (𝓤 : Universe) → ishinit 𝓤 ℤω-alg
ℤω-is-init univ 𝓤 A = pr₂ isContr-iff-is-inhabited-Prop ((ℤω-has-rec A) , (ℤω-has-rec-unique univ A))


-- III. The Integers as HIT

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

ℤₕ-≃ : ℤₕ ≃ ℤₕ
ℤₕ-≃ = (succₕ , predₕ , secₕ , retₕ , cohₕ)

ℤₕ-alg : Alg 𝓤₀
ℤₕ-alg = (ℤₕ , 0ₕ , succₕ , predₕ , secₕ , retₕ , cohₕ)

postulate

  -- (iii) Eliminator

  ℤₕ-ind : (E : FibAlg 𝓥 ℤₕ-alg) → (z : ℤₕ) → (pr₁ E) z

  -- (iv) Computation rules

  0-β : (E : FibAlg 𝓥 ℤₕ-alg) → ℤₕ-ind E 0ₕ ↦ pr₁ (pr₂ E)  

  {-# REWRITE 0-β #-}

  succ-β : (E : FibAlg 𝓥 ℤₕ-alg) (z : ℤₕ) → ℤₕ-ind E (succₕ z) ↦ pr₁ (pr₂ (pr₂ E)) z (ℤₕ-ind E z)

  {-# REWRITE succ-β #-}

ℤₕ-rec : (A : Alg 𝓤) → ℤₕ → pr₁ A
ℤₕ-rec (A , a₀ , s , i) = ℤₕ-ind ((λ - → A) , a₀ , (λ - → s) , λ - → i)

ℤₕ-is-ind : (𝓤 : Universe) → isind 𝓤 ℤₕ-alg
ℤₕ-is-ind 𝓤 (E , e₀ , s' , j) = let f = ℤₕ-ind (E , e₀ , s' , j) in
  f , (refl _) , (λ z → refl _)

ℤₕ-is-init : ishinit 𝓤₀ ℤₕ-alg
ℤₕ-is-init = isind-to-ishinit ℤₕ-alg (ℤₕ-is-ind 𝓤₀)

ℤₕ-is-ℤω : (univ : Univalence) → ℤₕ-alg ≡ ℤω-alg
ℤₕ-is-ℤω univ = ap pr₁ (InitAlg-is-Prop univ 𝓤₀ (ℤₕ-alg , ℤₕ-is-init) (ℤω-alg , ℤω-is-init univ 𝓤₀))

{-# OPTIONS --without-K --exact-split --safe #-}

open import Ch1.Type-theory
open import Ch2.Homotopy-type-theory
open import Ch3.Sets-and-logic
open import Ch4.Equivalences
open import Thesis.Z-Algebras
open import Thesis.Identity-types

module Thesis.Inductive-Z-Algebras where


-- I. Inductive Algebras

isind : (𝓥 : Universe) → Alg 𝓤 → 𝓤 ⊔ 𝓥 ⁺ ̇
isind 𝓥 A = (E : FibAlg 𝓥 A) → AlgSec A E

-- Dependent equalizer.

depEqz : (A : Alg 𝓤) (E : FibAlg 𝓤 A) → AlgSec A E → AlgSec A E → FibAlg 𝓤 A
depEqz {𝓤} (A , a₀ , s , p , σ , ρ , τ) (E , e₀ , s' , j) (f , f₀ , f-s) (g , g₀ , g-s) = Q , q₀ , t , k
  where
  i : isequiv s
  i = (p , σ , ρ , τ)
  p' : ((a : A) → E (s a) → E a)
  p' a = ishae₁ (j a)
  σ' : ((a : A) → (p' a) ∘ (s' a) ∼ id)
  σ' a = ishae₂ (j a)
  ρ' : ((a : A) → (s' a) ∘ (p' a) ∼ id)
  ρ' a = ishae₃ (j a)
  τ' : (a : A) (u : E a) → ap (s' a) (σ' a u) ≡ (ρ' a) (s' a u)
  τ' a = ishae₄ (j a)
  A' : Alg 𝓤
  A' = (A , a₀ , s , i)
  E' : FibAlg 𝓤 A'
  E' = (E , e₀ , s' , j)
  f' g' : AlgSec A' E'
  f' = (f , f₀ , f-s)
  g' = (g , g₀ , g-s)
  Q : A → 𝓤 ̇
  Q a = f a ≡ g a
  q₀ : Q a₀
  q₀ = f₀ ∙ g₀ ⁻¹  
  t : (a : A) → Q a → Q (s a)
  t a q = f-s a ∙ ap (s' a) q ∙ g-s a ⁻¹
  tinv : (a : A) → Q (s a) → Q a
  tinv a q = σ' a (f a) ⁻¹ ∙ ap (p' a) (f-s a ⁻¹ ∙ q ∙ g-s a) ∙ σ' a (g a)
  α : (a : A) → t a ∘ tinv a ∼ id
  α a q = ap (λ - → f-s a ∙ - ∙ g-s a ⁻¹) (ap-∙ (s' a) _ _ ∙ ((ap-∙ (s' a) _ _ ∙ ((ap-⁻¹ (s' a) _ ∙ ap _⁻¹ (τ' a (f a))) ∙ᵣ ap (s' a) _)) ✦ τ' a (g a))) ∙ aux (s' a) (p' a) (ρ' a) (f-s a) (g-s a) q where
    aux : {A : 𝓤 ̇} {B : 𝓥 ̇} (f : A → B) (g : B → A) (H : f ∘ g ∼ id) {b₁ b₁' b₂ b₂' : B} (p₁ : b₁ ≡ b₁') (p₂ : b₂ ≡ b₂') (q : b₁ ≡ b₂) → p₁ ∙ (H _ ⁻¹ ∙ ap f (ap g (p₁ ⁻¹ ∙ q ∙ p₂)) ∙ H _) ∙ p₂ ⁻¹ ≡ q
    aux f g H (refl _) (refl _) (refl _) = ru _ ⁻¹ ∙ lu _ ⁻¹ ∙ ((ru _ ⁻¹ ∙ᵣ H _) ∙ linv _)
  β : (a : A) → tinv a ∘ t a ∼ id
  β a q = aux (s' a) (p' a) (σ' a) (f-s a) (g-s a) q where
    aux : {A : 𝓤 ̇} {B : 𝓥 ̇} (f : A → B) (g : B → A) (H : g ∘ f ∼ id) {x y : A} {b₁ b₂ : B} (p₁ : b₁ ≡ _) (p₂ : b₂ ≡ _) (q : x ≡ y) → H x ⁻¹ ∙ ap g (p₁ ⁻¹ ∙ (p₁ ∙ ap f q ∙ p₂ ⁻¹) ∙ p₂) ∙ H y ≡ q
    aux f g H (refl .(f _)) (refl .(f _)) (refl _) = (ru _ ⁻¹ ∙ᵣ H _) ∙ linv _
  k : (a : A) → ishae (t a)
  k a = qinv-to-isequiv (tinv a , α a , β a)

uniqueness-pple : ⦃ fe : FunExt ⦄ (A : Alg 𝓤) → isind 𝓤 A → (E : FibAlg 𝓤 A) → isProp (AlgSec A E)
uniqueness-pple A A-ind E f g = Sec-≡-intro A E f g (A-ind (depEqz A E f g))

isind-is-Prop : ⦃ fe : FunExt ⦄ (A : Alg 𝓤) → isProp (isind 𝓤 A)
isind-is-Prop {𝓤} A A-ind = aux A-ind
  where
  aux : isProp (isind 𝓤 A)
  aux = Π-preserves-Props _ (λ E → uniqueness-pple A A-ind E)

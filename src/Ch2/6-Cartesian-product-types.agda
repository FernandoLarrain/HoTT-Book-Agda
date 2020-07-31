{-# OPTIONS --without-K --exact-split --safe #-}

open import Ch1.Type-theory
open import Ch2.1-Types-are-higher-groupoids
open import Ch2.2-Functions-are-functors
open import Ch2.3-Type-families-are-fibrations
open import Ch2.4-Homotopies-and-equivalences

module Ch2.6-Cartesian-product-types where


-- Theorem 2.6.2 (Equalities of pairs are pairs of equalities).

module _ {A : 𝓤 ̇} {B : 𝓥 ̇} {x y : A × B} where

  -- (i) From pair of equalities to equality of pairs

  pair-≡ : (pr₁ x ≡ pr₁ y) × (pr₂ x ≡ pr₂ y) → x ≡ y
  pair-≡ (refl _ , refl _) = refl _

  -- (ii) From equality of pairs to pair of equalities

  pr-≡ : x ≡ y → (pr₁ x ≡ pr₁ y) × (pr₂ x ≡ pr₂ y)
  pr-≡ = ⟨ ap pr₁ , ap pr₂ ⟩

  -- (iii) Propositional computation rules for equality of pairs

  ap-pr₁-β : (p : pr₁ x ≡ pr₁ y) (q : pr₂ x ≡ pr₂ y) → ap pr₁ (pair-≡ (p , q)) ≡ p
  ap-pr₁-β (refl _) (refl _) = refl (refl _)

  ap-pr₂-β : (p : pr₁ x ≡ pr₁ y) (q : pr₂ x ≡ pr₂ y) → ap pr₂ (pair-≡ (p , q)) ≡ q
  ap-pr₂-β (refl _) (refl _) = refl (refl _)

  pr-≡-β : (p : pr₁ x ≡ pr₁ y) (q : pr₂ x ≡ pr₂ y) → pr-≡ (pair-≡ (p , q)) ≡ p , q
  pr-≡-β (refl _) (refl _) = refl (refl _ , refl _)

  -- (iv) Propositional uniqueness principle for equality of pairs

  ×-≡-η : (r : x ≡ y) → pair-≡ (ap pr₁ r , ap pr₂ r) ≡ r
  ×-≡-η (refl x) = refl (refl x)

  -- (v) Thm. 2.6.7 proper

  qinv-pr-≡ : qinv (pr-≡)
  qinv-pr-≡ = pair-≡ , (Σ-induction λ p q → pr-≡-β p q) , ×-≡-η


-- Propositional uniqueness principle for pairs

×-η : {A : 𝓤 ̇} {B : 𝓥 ̇} (z : A × B) → z ≡ (pr₁ z , pr₂ z)
×-η z = pair-≡ (refl _ , refl _)

{- Note that we also have a judgemental or definitional uniqueness principle for pairs: -}

_ : {A : 𝓤 ̇} {B : 𝓥 ̇} (z : A × B) → z ≡ (pr₁ z , pr₂ z)
_ = hrefl id


-- Componentwise characterization of refl, _⁻¹ and _∙_

module _ {A : 𝓤 ̇} {B : 𝓥 ̇} where

  pair-refl : (z : A × B) → refl z ≡ pair-≡ (refl (pr₁ z) , refl (pr₂ z))
  pair-refl (a , b) = refl (refl (a , b))

  pair-⁻¹ : {x y : A × B} (p : x ≡ y) → p ⁻¹ ≡ pair-≡ ((ap pr₁ p ⁻¹) , (ap pr₂ p ⁻¹))
  pair-⁻¹ (refl (a , b)) = refl (refl (a , b))

  pair-∙ : {x y z : A × B} (p : x ≡ y) (q : y ≡ z) → p ∙ q ≡ pair-≡ ((ap pr₁ p ∙ ap pr₁ q) , (ap pr₂ p ∙ ap pr₂ q))
  pair-∙ (refl (a , b)) (refl (a , b)) = refl (refl (a , b))


-- Theorem 2.6.4 (Transport of pairs).

transport-pair : {Z : 𝓤 ̇} (A B : Z → 𝓥 ̇) {z w : Z} (p : z ≡ w) → transport (λ z → A z × B z) p ∼ ⟨ transport A p × transport B p ⟩
transport-pair A B (refl z) (a , b) = refl (a , b)


-- Theorem 2.6.5 (Functoriality of ap under products).

ap-pair : {A : 𝓤 ̇} {B : 𝓥 ̇} {A' : 𝓦 ̇} {B' : 𝓣 ̇} (g : A → A') (h : B → B') {x y : A × B} (p : pr₁ x ≡ pr₁ y) (q : pr₂ x ≡ pr₂ y) → ap ⟨ g × h ⟩ (pair-≡ (p , q)) ≡ pair-≡ (ap g p , ap h q)
ap-pair g h {a , b} {a , b} (refl a) (refl b) = refl _

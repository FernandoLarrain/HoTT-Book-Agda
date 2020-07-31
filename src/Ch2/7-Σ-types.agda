{-# OPTIONS --without-K --exact-split --safe #-}

open import Ch1.Type-theory
open import Ch2.1-Types-are-higher-groupoids
open import Ch2.2-Functions-are-functors 
open import Ch2.3-Type-families-are-fibrations
open import Ch2.4-Homotopies-and-equivalences

module Ch2.7-Σ-types where


-- Theorem 2.7.2 (Equalities of dependent pairs are dependent pairs of equalities).

module _ {A : 𝓤 ̇} {P : A → 𝓥 ̇} {w w' : Σ x ꞉ A , P x} where

  -- (i) From dependent pair of equalities to equality of dependent pairs

  dpair-≡ : Σ p ꞉ pr₁ w ≡ pr₁ w' , (transport P p (pr₂ w) ≡ pr₂ w')  → w ≡ w'
  dpair-≡ (refl _ , refl _) = refl _

  -- (ii) Form equality of dependent pairs to dependent pair of equalities

  -- (ii).1 Definition of dpair-≡ via path induction

  dpr-≡ : w ≡ w' → Σ p ꞉ pr₁ w ≡ pr₁ w' , (transport P p (pr₂ w) ≡ pr₂ w')
  dpr-≡ (refl w) = (refl _) , (refl _)

  -- (ii).2 Definition of dpair-≡ via pairing

  dpr-≡' : w ≡ w' → Σ p ꞉ pr₁ w ≡ pr₁ w' , (transport P p (pr₂ w) ≡ pr₂ w')
  dpr-≡' r = (ap pr₁ r) , (transport-∘ P pr₁ r (pr₂ w) ⁻¹ ∙ apd pr₂ r)

  -- (ii).3 Definitions 1 and 2 agree

  dpr-≡-agreement : (r : w ≡ w') → dpr-≡ r ≡ dpr-≡' r
  dpr-≡-agreement (refl w) = refl ((refl _) , (refl _))

  -- (iii) Propositional computation rules for equality of dependent pairs

  Σ-≡-β : (r : Σ p ꞉ pr₁ w ≡ pr₁ w' , (transport P p (pr₂ w) ≡ pr₂ w')) → dpr-≡ (dpair-≡ r) ≡ r
  Σ-≡-β (refl _ , refl _) = refl ((refl _) , (refl _))

  dpr₁-≡-β : (p : pr₁ w ≡ pr₁ w') (q : transport P p (pr₂ w) ≡ pr₂ w') → ap pr₁ (dpair-≡ (p , q)) ≡ p
  dpr₁-≡-β (refl _) (refl _) = refl (refl _)

  -- (iv) Propositional uniqueness rules for equality of dependent pairs

  Σ-≡-η : (p : w ≡ w') → dpair-≡ (dpr-≡ p) ≡ p
  Σ-≡-η (refl (x , y)) = refl (refl (x , y))

  Σ-≡-η' : (p : w ≡ w') → dpair-≡ (dpr-≡' p) ≡ p
  Σ-≡-η'(refl (x , y)) = refl (refl (x , y))

  -- (v) Thm. 2.7.2 proper

  Σ-≡-equiv : (w ≡ w') ≃ (Σ p ꞉ pr₁ w ≡ pr₁ w' , (transport P p (pr₂ w) ≡ pr₂ w'))
  Σ-≡-equiv = dpr-≡ , qinv-to-isequiv (dpair-≡ , (Σ-≡-β , Σ-≡-η))

-- Corollary 2.7.3 (Propositional uniqueness principle for dependent pairs).

Σ-η : {A : 𝓤 ̇} {P : A → 𝓥 ̇} (z : Σ x ꞉ A , P x) → z ≡ (pr₁ z , pr₂ z)
Σ-η z = dpair-≡ ((refl (pr₁ z)) , (refl (pr₂ z)))

{- Note that we also have a judgemental uniqueness principle for dependent pairs : -}

_ : {A : 𝓤 ̇} {P : A → 𝓥 ̇} (z : Σ x ꞉ A , P x) → z ≡ (pr₁ z , pr₂ z)
_ = hrefl id


-- Theorem 2.7.4 (Action of transport on Σ-types).

transport-dpair : {A : 𝓤 ̇} {P : A → 𝓥 ̇} {Q : Σ P → 𝓦 ̇} {x y : A} (p : x ≡ y) (u : P x) (z : Q (x , u)) → transport (λ x → Σ v ꞉ P x , Q (x , v)) p (u , z) ≡ transport P p u , transport Q (dpair-≡ (p , refl (transport P p u))) z
transport-dpair (refl x) u z = refl (u , z)


-- Componentwise characterization of refl, _⁻¹ and _∙_

module _ {A : 𝓤 ̇} {B : A → 𝓥 ̇} where

  dpair-refl : (z : Σ B) → refl z ≡ dpair-≡ (refl (pr₁ z) , refl (pr₂ z))
  dpair-refl (a , b) = refl (refl (a , b))

  -- TO-DO: _⁻¹ , _∙_

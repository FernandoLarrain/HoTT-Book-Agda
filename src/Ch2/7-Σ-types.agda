{-# OPTIONS --without-K --exact-split --safe #-}

open import Ch1.Type-theory
open import Ch2.1-Types-are-higher-groupoids
open import Ch2.2-Functions-are-functors 
open import Ch2.3-Type-families-are-fibrations
open import Ch2.4-Homotopies-and-equivalences

module Ch2.7-Σ-types where


-- Theorem 2.7.2 (Equalities of dependent pairs are dependent pairs of equalities).

-- (i) From dependent pair of equalities to equality of dependent pairs

dpair-≡ : {A : 𝓤 ̇ } {P : A → 𝓥 ̇ } {w w' : Σ x ꞉ A , P x} → Σ p ꞉ pr₁ w ≡ pr₁ w' , (transport P p (pr₂ w) ≡ pr₂ w')  → w ≡ w'
dpair-≡ {w = w₁ , w₂} {.w₁ , .w₂} (refl .w₁ , refl .w₂) = refl (w₁ , w₂)

-- (ii) Form equality of dependent pairs to dependent pair of equalities

-- (ii).1 Definition of dpair-≡ via path induction

dpr-≡ : {A : 𝓤 ̇ } {P : A → 𝓥 ̇ } {w w' : Σ x ꞉ A , P x} → w ≡ w' → Σ p ꞉ pr₁ w ≡ pr₁ w' , (transport P p (pr₂ w) ≡ pr₂ w')
dpr-≡ {P = P} {.w} {.w} (refl w) = (refl _) , (refl _)

-- (ii).2 Definition of dpair-≡ via pairing

dpr-≡' : {A : 𝓤 ̇ } {P : A → 𝓥 ̇ } {w w' : Σ x ꞉ A , P x} → w ≡ w' → Σ p ꞉ pr₁ w ≡ pr₁ w' , (transport P p (pr₂ w) ≡ pr₂ w')
dpr-≡' {P = P} {w} {w'} r = (ap pr₁ r) , (transport-∘ P pr₁ r (pr₂ w) ⁻¹ ∙ apd pr₂ r)

-- (ii).3 Definitions 1 and 2 agree

dpr-≡-agreement : {A : 𝓤 ̇ } {P : A → 𝓥 ̇ } {w w' : Σ x ꞉ A , P x} (r : w ≡ w') → dpr-≡ r ≡ dpr-≡' r
dpr-≡-agreement (refl w) = refl ((refl _) , (refl _))

-- (iii) Propositional computation rules for equality of dependent pairs

Σ-≡-β : {A : 𝓤 ̇ } {P : A → 𝓥 ̇ } {w w' : Σ x ꞉ A , P x} (r : Σ p ꞉ pr₁ w ≡ pr₁ w' , (transport P p (pr₂ w) ≡ pr₂ w')) → dpr-≡ (dpair-≡ r) ≡ r
Σ-≡-β {w = w₁ , w₂} {.w₁ , .w₂} (refl .w₁ , refl .w₂) = refl ((refl w₁) , (refl w₂))

dpr₁-≡-β : {A : 𝓤 ̇ } {P : A → 𝓥 ̇ } {w w' : Σ x ꞉ A , P x} (p : pr₁ w ≡ pr₁ w') (q : transport P p (pr₂ w) ≡ pr₂ w') → ap pr₁ (dpair-≡ (p , q)) ≡ p
dpr₁-≡-β {w = w₁ , w₂} {.w₁ , .w₂} (refl .w₁) (refl .w₂) = refl (refl w₁)

-- (iv) Propositional uniqueness rules for equality of dependent pairs

Σ-≡-η : {A : 𝓤 ̇ } {P : A → 𝓥 ̇ } {w w' : Σ x ꞉ A , P x}  (p : w ≡ w') → dpair-≡ (dpr-≡ p) ≡ p
Σ-≡-η {w = .(x , y)} {.(x , y)} (refl (x , y)) = refl (refl (x , y))

Σ-≡-η' : {A : 𝓤 ̇ } {P : A → 𝓥 ̇ } {w w' : Σ x ꞉ A , P x}  (p : w ≡ w') → dpair-≡ (dpr-≡' p) ≡ p
Σ-≡-η' {w = .(x , y)} {.(x , y)} (refl (x , y)) = refl (refl (x , y))

-- (v) Thm. 2.7.2 proper

Σ-≡-equiv : {A : 𝓤 ̇ } {P : A → 𝓥 ̇ } (w w' : Σ x ꞉ A , P x) → (w ≡ w') ≃ (Σ p ꞉ pr₁ w ≡ pr₁ w' , (transport P p (pr₂ w) ≡ pr₂ w'))
Σ-≡-equiv w w' = dpr-≡ , qinv-to-isequiv (dpair-≡ , (Σ-≡-β , Σ-≡-η))


-- Corollary 2.7.3 (Propositional uniqueness principle for dependent pairs).

Σ-η : {A : 𝓤 ̇ } {P : A → 𝓥 ̇ } (z : Σ x ꞉ A , P x) → z ≡ (pr₁ z , pr₂ z)
Σ-η z = dpair-≡ ((refl (pr₁ z)) , (refl (pr₂ z)))


-- Theorem 2.7.4 (Action of transport on Σ-types).

transport-dpair : {A : 𝓤 ̇ } {P : A → 𝓥 ̇ } {Q : Σ P → 𝓦 ̇ } {x y : A} (p : x ≡ y) (u : P x) (z : Q (x , u)) → transport (λ x → Σ v ꞉ P x , Q (x , v)) p (u , z) ≡ transport P p u , transport Q (dpair-≡ (p , refl (transport P p u))) z
transport-dpair (refl x) u z = refl (u , z)


-- Componentwise characterization of refl

dpair-refl : {A : 𝓤 ̇ } {B : A → 𝓥 ̇ } (z : Σ B) → refl z ≡ dpair-≡ (refl (pr₁ z) , refl (pr₂ z))
dpair-refl (a , b) = refl (refl (a , b))

{-# OPTIONS --without-K --exact-split #-}

open import Ch1.Type-theory
open import Ch2.Homotopy-type-theory
open import Ch3.Sets-and-logic

module Ch5.4-Inductive-types-are-initial-algebras where

-- Definition 5.4.1 (ℕ-algebra).

ℕAlg : (𝓤 : Universe) → 𝓤 ⁺ ̇    
ℕAlg 𝓤 = Σ C ꞉ 𝓤 ̇ , C × (C → C)


-- Definition 5.4.2 (ℕ-homomorphism).

ℕHom : ℕAlg 𝓤 → ℕAlg 𝓤 → 𝓤 ̇ 
ℕHom (C , c₀ , cs) (D , d₀ , ds) = Σ h ꞉ (C → D) , (h c₀ ≡ d₀) × (h ∘ cs ∼ ds ∘ h)

_∘ℕ_ : {C D E : ℕAlg 𝓤} → ℕHom D E → ℕHom C D → ℕHom C E
_∘ℕ_ {C = C , c₀ , cs} {D , d₀ , ds} {E , e₀ , es} (g , q , β) (f , p , α) = (g ∘ f) , (ap g p ∙ q) , λ x → ap g (α x) ∙ β (f x)

infixl 70 _∘ℕ_

ℕAlg-id : (C : ℕAlg 𝓤) → ℕHom C C
ℕAlg-id (C , c₀ , cs) = id , (refl _) , (refl ∘ cs)

 
-- Definition 5.4.3 (homotopy-initial ℕ-algebra).

isHinit-ℕ : ℕAlg 𝓤 → 𝓤 ⁺ ̇
isHinit-ℕ {𝓤} I = (C : ℕAlg 𝓤) → isContr (ℕHom I C) 

isHinit-ℕ-is-Prop : (I : ℕAlg 𝓤) → isProp (isHinit-ℕ I)
isHinit-ℕ-is-Prop I = Π-preserves-Props _ (λ C → isContr-is-Prop _)

Hinit-ℕAlg : (𝓤 : Universe) → 𝓤 ⁺ ̇
Hinit-ℕAlg 𝓤 = Σ C ꞉ ℕAlg 𝓤 , isHinit-ℕ C


-- Theorem 5.4.4 (h-inital ℕ-algebras are equal).

Hinit-ℕAlg-is-Prop : isProp (Hinit-ℕAlg 𝓤)
Hinit-ℕAlg-is-Prop {𝓤} ((UI , i₀ , is) , i) ((UJ , j₀ , js) , j) = Σ-over-predicate _ _ isHinit-ℕ-is-Prop _ _ (dpair-≡ (
  carrier-≡ ,
  (transport-pair id (λ X → X → X) carrier-≡ (i₀ , is) ∙ pair-≡ (
    point-≡ ,
    homotopy-≡
    )
  )))
  where
  I = (UI , i₀ , is)
  J = (UJ , j₀ , js)
  f : ℕHom I J
  f = pr₁ (i J)
  Uf = pr₁ f
  p = pr₁ (pr₂ f)
  α = pr₂ (pr₂ f)
  g : ℕHom J I  
  g = pr₁ (j I)
  Ug = pr₁ g
  q = pr₁ (pr₂ g)
  β = pr₂ (pr₂ g)
  p' : _∘ℕ_ {E = I} g f ≡ ℕAlg-id I
  p' = pr₂ (pr₁ (isContr-iff-is-inhabited-Prop (ℕHom I I)) (i I)) _ _
  q' : _∘ℕ_ {E = J} f g ≡ ℕAlg-id J
  q' = pr₂ (pr₁ (isContr-iff-is-inhabited-Prop (ℕHom J J)) (j J)) _ _
  carrier-≃ : UI ≃ UJ
  carrier-≃ = Uf , (qinv-to-isequiv (Ug , happly _ _ (pr₁ (dpr-≡ q')) , happly _ _ (pr₁ (dpr-≡ p'))))
  carrier-≡ : UI ≡ UJ
  carrier-≡ = ua UI UJ (carrier-≃)
  point-≡ : coe carrier-≡ i₀ ≡ j₀
  point-≡ = idtoeqv-β _ _ carrier-≃ i₀ ∙ p
  homotopy-≡ : transport (λ X → X → X) carrier-≡ is ≡ js
  homotopy-≡ = funext _ _ λ y → transport-fun' {X = 𝓤 ̇} {id} {id} UI UJ carrier-≡ is y ∙ (idtoeqv-β _ _ carrier-≃ (is (coe (carrier-≡ ⁻¹) y)) ∙ (ap (Uf ∘ is) (happly _ _ (ap coe (type-sym carrier-≃) ∙ funext _ _ (idtoeqv-β _ _ (≃-sym carrier-≃))) y) ∙ (α (Ug y) ∙ ap js (happly _ _ (pr₁ (dpr-≡ q')) y))))
  
-- TO DO

-- 1. Why is Agda unable to infer codomain of composite? There seems to be a problem with the third component of the algebra (the homotopy). E.g.

postulate
  C D : ℕAlg 𝓤
  g : ℕHom (D {𝓤}) (C {𝓤})
  f : ℕHom (C {𝓤}) (D {𝓤})
  p : _∘ℕ_ {E = C} g f ≡ ℕAlg-id (C {𝓤})  

-- 2. The proof seems to rely on some sort of SIP, because it deduces that I = J from the existence of an "equivalence homomorphism". See Ch2.14. Perhaps this is not necessary but it would be useful to work out the properties of equivalence homomorphisms in general.

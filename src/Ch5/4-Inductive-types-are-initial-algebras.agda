{-# OPTIONS --without-K --exact-split #-}

open import Ch1.Type-theory
open import Ch2.Homotopy-type-theory
open import Ch3.Sets-and-logic

module Ch5.4-Inductive-types-are-initial-algebras where


-- Definition 5.4.1 (ℕ-algebra).

ℕAlg : (𝓤 : Universe) → 𝓤 ⁺ ̇ 
ℕAlg 𝓤 = Σ C ꞉ 𝓤 ̇ , C × (C → C)


-- Definition 5.4.2 (ℕ-homomorphism).

-- Using Σ-types:

ℕHom : ℕAlg 𝓤 → ℕAlg 𝓤 → 𝓤 ̇
ℕHom (C , c₀ , cs) (D , d₀ , ds) = Σ h ꞉ (C → D) , (h c₀ ≡ d₀) × (h ∘ cs ∼ ds ∘ h)

_∘ℕ_ : {C D E : ℕAlg 𝓤} → ℕHom D E → ℕHom C D → ℕHom C E
_∘ℕ_ (g , q , β) (f , p , α) = (g ∘ f) , (ap g p ∙ q) , λ x → ap g (α x) ∙ β (f x)

module _ (C D : ℕAlg 𝓤) (f : ℕHom C D) (g : ℕHom D C) where

  _ : ℕHom C C
  _ = _∘ℕ_ {E = _ , _ , pr₂ (pr₂ C)} g f -- problem with inference of implicit arguments

-- Using records: ----------------------------------------------------------

record ℕHom' (C : ℕAlg 𝓤) (D : ℕAlg 𝓤) : 𝓤 ̇ where
  field
    f : pr₁ C → pr₁ D
    p : f (pr₁ (pr₂ C)) ≡ pr₁ (pr₂ (D)) 
    α : f ∘ pr₂ (pr₂ C) ∼ pr₂ (pr₂ D) ∘ f 

_∘ℕ'_ : {C D E : ℕAlg 𝓤} → ℕHom' D E → ℕHom' C D → ℕHom' C E
_∘ℕ'_ record { f = g ; p = q ; α = β } record { f = f ; p = p ; α = α } = record { f = g ∘ f ; p =  ap g p ∙ q ; α = λ x → ap g (α x) ∙ β (f x) }

module _ (C D : ℕAlg 𝓤) (f : ℕHom' C D) (g : ℕHom' D C) where

  _ : ℕHom' C C
  _ =  g ∘ℕ' f -- no problem with inference of implicit arguments
 
----------------------------------------------------------------------------

infixl 70 _∘ℕ_

ℕAlg-id : (C : ℕAlg 𝓤) → ℕHom C C
ℕAlg-id (C , c₀ , cs) = id , (refl c₀) , hrefl cs


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

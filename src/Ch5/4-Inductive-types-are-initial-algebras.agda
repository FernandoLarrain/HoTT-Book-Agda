{-# OPTIONS --without-K --exact-split #-}

open import Ch1.Type-theory
open import Ch2.Homotopy-type-theory
open import Ch3.Sets-and-logic
open import Ch5.1-Introduction-to-inductive-types

module Ch5.4-Inductive-types-are-initial-algebras where


-- Definition 5.4.1 (ℕ-algebra).

ℕAlg : (𝓤 : Universe) → 𝓤 ⁺ ̇ 
ℕAlg 𝓤 = Σ C ꞉ 𝓤 ̇ , C × (C → C)


-- Definition 5.4.2 (ℕ-homomorphism).

is-ℕAlg-homomorphism : (C D : ℕAlg 𝓤) → (pr₁ C → pr₁ D) → 𝓤 ̇
is-ℕAlg-homomorphism {𝓤} (C , c₀ , cs) (D , d₀ , ds) h = (h c₀ ≡ d₀) × (h ∘ cs ∼ ds ∘ h)

ℕHom : ℕAlg 𝓤 → ℕAlg 𝓤 → 𝓤 ̇
ℕHom C D = Σ h ꞉ (pr₁ C → pr₁ D) , is-ℕAlg-homomorphism C D h

ℕHom-comp : (C D E : ℕAlg 𝓤) → ℕHom D E → ℕHom C D → ℕHom C E
ℕHom-comp C D E (g , q , β) (f , p , α) = (g ∘ f) , (ap g p ∙ q) , λ x → ap g (α x) ∙ β (f x)

ℕAlg-id : (C : ℕAlg 𝓤) → ℕHom C C
ℕAlg-id (C , c₀ , cs) = id , (refl c₀) , hrefl cs


-- Isomorphic ℕ-algebras are equal.

_ℕAlg-≅_ : ℕAlg 𝓤 → ℕAlg 𝓤 → 𝓤 ̇
C ℕAlg-≅ D = Σ f ꞉ ℕHom C D , Σ g ꞉ ℕHom D C , (ℕHom-comp D C D f g ≡ ℕAlg-id D) × (ℕHom-comp C D C g f ≡ ℕAlg-id C)

ℕAlg-≅-to-≃ : {C D : ℕAlg 𝓤} → C ℕAlg-≅ D → pr₁ C ≃ pr₁ D
ℕAlg-≅-to-≃ ((f , f-is-hom) , (g , g-is-hom) , p , q) with dpr-≡ p | dpr-≡ q
... | (p' , p-etc) | (q' , q-etc) = f , qinv-to-isequiv (g , (happly p' , happly q'))

ℕAlg-≅-to-≡ : ⦃ fe : FunExt ⦄ ⦃ univ : Univalence ⦄ {C D : ℕAlg 𝓤} → C ℕAlg-≅ D → C ≡ D
ℕAlg-≅-to-≡ {𝓤} {C , c₀ , cs} {D , d₀ , ds} ((f , p , α) , (g , q , β) , p' , q') = dpair-≡ (carrier-≡ , (transport-pair id (λ X → X → X) carrier-≡ (c₀ , cs) ∙ pair-≡ (zero-≡ , succ-≡))) where
  carrier-≃ : C ≃ D
  carrier-≃ = ℕAlg-≅-to-≃ ((f , p , α) , (g , q , β) , p' , q')
  carrier-≡ : C ≡ D
  carrier-≡ = ua carrier-≃
  zero-≡ : coe carrier-≡ c₀ ≡ d₀
  zero-≡ = idtoeqv-β carrier-≃ c₀ ∙ p 
  succ-≡ : transport (λ X → X → X) carrier-≡ cs ≡ ds
  succ-≡ = funext (λ d → transport-fun carrier-≡ cs d ∙ (idtoeqv-β carrier-≃ (cs (coe (carrier-≡ ⁻¹) d)) ∙ (ap (f ∘ cs) (happly (ap coe (type-sym carrier-≃) ∙ funext (idtoeqv-β (≃-sym carrier-≃))) d) ∙ (α (g d) ∙ ap ds (happly (pr₁ (dpr-≡ p')) d)))))


-- Definition 5.4.3 (homotopy-initial ℕ-algebra).

isHinit-ℕ : ℕAlg 𝓤 → 𝓤 ⁺ ̇
isHinit-ℕ {𝓤} I = (C : ℕAlg 𝓤) → isContr (ℕHom I C) 

isHinit-ℕ-is-Prop : ⦃ fe : FunExt ⦄ (I : ℕAlg 𝓤) → isProp (isHinit-ℕ I)
isHinit-ℕ-is-Prop I = Π-preserves-Props _ (λ C → isContr-is-Prop _)

Hinit-ℕAlg : (𝓤 : Universe) → 𝓤 ⁺ ̇
Hinit-ℕAlg 𝓤 = Σ C ꞉ ℕAlg 𝓤 , isHinit-ℕ C


-- Theorem 5.4.4 (h-inital ℕ-algebras are equal).

Hinit-ℕAlg-is-Prop : ⦃ fe : FunExt ⦄ ⦃ univ : Univalence ⦄ → isProp (Hinit-ℕAlg 𝓤)
Hinit-ℕAlg-is-Prop {𝓤} ((UI , i₀ , is) , i) ((UJ , j₀ , js) , j) =
  let I = (UI , i₀ , is)
      J = (UJ , j₀ , js)
  in Σ-over-predicate isHinit-ℕ-is-Prop _ _ (ℕAlg-≅-to-≡ (
  pr₁ (i J) ,
  pr₁ (j I) ,
  pr₂ (pr₁ isContr-iff-is-inhabited-Prop  (j J)) _ _ ,
  pr₂ (pr₁ isContr-iff-is-inhabited-Prop (i I)) _ _
  ))


-- Theorem 5.4.5 ((ℕ , 0 , succ) is h-initial)

-- Need to characterize equality of ℕHom (being a homomorphism is a property, so the uniqueness thm 5.1.1 suffices by Lemma 3.5.1).

-- Is being an ℕHom a property? 

-- ℕ-is-h-initial : isHinit-ℕ (ℕ , 0 , succ)
-- ℕ-is-h-initial (C , c₀ , cs) =
--   (f , p , α) ,
--   contraction
--   where
--   f : ℕ → C
--   f = ℕ-recursion C c₀ (λ n → cs)
--   p : f 0 ≡ c₀
--   p = refl _
--   α : f ∘ succ ∼ cs ∘ f
--   α zero = refl _
--   α (succ n) = ap cs (α n) 
--   contraction : Π (_≡_ (f , p , α))
--   contraction (g , q , β) = let fun-≡ = ℕ-η (λ - → C) c₀ (λ n → cs) f g p α q β
--     in dpair-≡ (
--       fun-≡ ,
--       (transport-pair {𝓤₀} {𝓤₀} {ℕ → C} (λ h → h 0 ≡ c₀) (λ h → h ∘ succ ∼ cs ∘ h) fun-≡ (p , α) ∙ pair-≡ (
--         {!!} , 
--         {!!}  -- non-trivial... maybe we should do 5.8 first, because the book is really sketchy in the parts involving homomorphisms.
--         ))
--       )

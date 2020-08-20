{-# OPTIONS --without-K --exact-split --safe #-}

open import Ch1.Type-theory
open import Ch2.Homotopy-type-theory
open import Ch3.Sets-and-logic
open import Ch4.2-Half-adjoint-equivalences
open import Ch4.4-Contractible-fibers

module Ch4.6-Surjections-and-embeddings where


-- Definition 4.6.1 (Surjections and embeddings)

isSurjective : ⦃ pt : PropTrunc ⦄ {A : 𝓤 ̇} {B : 𝓥 ̇} → (A → B) → 𝓤 ⊔ 𝓥 ̇
isSurjective {𝓤} {𝓥} {A} {B} f = (b : B) → ∃ a ꞉ A , (f a ≡ b)

isSurjective-is-Prop : ⦃ fe : FunExt ⦄ ⦃ pt : PropTrunc ⦄ {A : 𝓤 ̇} {B : 𝓥 ̇} (f : A → B) → isProp (isSurjective f)
isSurjective-is-Prop f = Π-preserves-Props _ λ y → ∃-is-Prop 

isEmbedding : {A : 𝓤 ̇} {B : 𝓥 ̇} → (A → B) → 𝓤 ⊔ 𝓥 ̇
isEmbedding {𝓤} {𝓥} {A} {B} f = (x y : A) → isequiv (ap f {x} {y})  

_↪_ : 𝓤 ̇ → 𝓥 ̇ → 𝓤 ⊔ 𝓥 ̇
A ↪ B = Σ f ꞉ (A → B) , isEmbedding f

isInjective : {A : 𝓤 ̇} {B : 𝓥 ̇} → (A → B) → 𝓤 ⊔ 𝓥 ̇
isInjective {𝓤} {𝓥} {A} {B} f = (x y : A) → f x ≡ f y → x ≡ y

module _ ⦃ fe : FunExt ⦄ {A : 𝓤 ̇} {B : 𝓥 ̇} where

  isEmbedding-is-Prop : (f : A → B) → isProp (isEmbedding f)
  isEmbedding-is-Prop f = Π-preserves-Props _ λ x → Π-preserves-Props _ λ y → ishae-is-Prop _

  injectivity-in-Set-is-Prop : isSet A → (f : A → B) → isProp (isInjective f)
  injectivity-in-Set-is-Prop A-is-Set f f-is-injective f-is-injective' = funext λ x → funext λ y → funext λ p → A-is-Set _ _ _ _
  
  embedding-of-sets-is-injection : isSet A → isSet B → (f : A → B) → (isEmbedding f ≃ isInjective f)
  embedding-of-sets-is-injection A-is-Set B-is-Set f = ⇔-to-≃ (isEmbedding-is-Prop _) (injectivity-in-Set-is-Prop A-is-Set _) (sufficiency , necessity)
    where
    sufficiency : isEmbedding f → isInjective f
    sufficiency f-is-embedding x y p = ap-f-inv p where
      ap-f-inv = isequiv₁ (f-is-embedding x y)
    necessity : isInjective f → isEmbedding f
    necessity f-is-injective x y = qinv-to-isequiv (
      f-is-injective x y ,
      (λ p → B-is-Set _ _ _ _) ,
      λ p → A-is-Set _ _ _ _
      )


{- Before proving theorem 4.6.3, we anticipate some results from chapter 7 that will simplify proofs involving universe lifting. -}

-- Definition (Propositional maps).

isPropMap : {A : 𝓤 ̇} {B : 𝓥 ̇} → (A → B) → 𝓤 ⊔ 𝓥 ̇
isPropMap {𝓤} {𝓥} {A} {B} f = (y : B) → isProp (fib f y)

isPropMap-is-Prop : ⦃ fe : FunExt ⦄ {A : 𝓤 ̇} {B : 𝓥 ̇} (f : A → B) → isProp (isPropMap f)
isPropMap-is-Prop f = Π-preserves-Props _ (λ y → isProp-is-Prop _)


-- Propositional maps are precisely embeddings.

isPropMap-to-isEmbedding : {A : 𝓤 ̇} {B : 𝓥 ̇} (f : A → B) → isPropMap f → isEmbedding f
isPropMap-to-isEmbedding f f-is-Prop x x' = isContrMap-to-ishae _ (λ p → ≃-preserves-Contr (≃-sym (fib-of-ap-is-path-space-fib p)) (pr₁ Prop-iff-Contr-≡ (f-is-Prop (f x')) (x , p) (x' , refl (f x')))) 

isEmbedding-to-isPropMap : {A : 𝓤 ̇} {B : 𝓥 ̇} (f : A → B) → isEmbedding f → isPropMap f
isEmbedding-to-isPropMap f f-is-embedding y = pr₂ Prop-iff-Contr-≡ (λ w w' → ≃-preserves-Contr (≃-sym (path-space-fib-is-fib-of-ap w w')) (ishae-to-isContrMap _ (f-is-embedding (pr₁ w) (pr₁ w')) _))

isEmbedding-≃-isPropMap : ⦃ fe : FunExt ⦄ {A : 𝓤 ̇} {B : 𝓥 ̇} (f : A → B) → isEmbedding f ≃ isPropMap f
isEmbedding-≃-isPropMap f = ⇔-to-≃ (isEmbedding-is-Prop f) (isPropMap-is-Prop f) (isEmbedding-to-isPropMap f , isPropMap-to-isEmbedding f)  


-- Theorem 4.6.3 / Corollary 4.6.4 (Equivalences are surjective embeddings)

isequiv-≃-is-surjective-embedding : ⦃ fe : FunExt ⦄ ⦃ pt : PropTrunc ⦄ {A : 𝓤 ̇} {B : 𝓥 ̇} (f : A → B) → isequiv f ≃ (isSurjective f × isEmbedding f)
isequiv-≃-is-surjective-embedding f = ⇔-to-≃ (ishae-is-Prop _) (×-preserves-Props _ _ (isSurjective-is-Prop _) (isEmbedding-is-Prop _)) (sufficiency , necessity) where
  sufficiency :  isequiv f → isSurjective f × isEmbedding f
  sufficiency f-is-equiv = (λ b → ∣ (pr₁ (ishae-to-isContrMap _ f-is-equiv b)) ∣₋₁) , ap-of-equiv-is-equiv f-is-equiv
  necessity : isSurjective f × isEmbedding f → isequiv f
  necessity (f-is-surjective , f-is-embedding) = isContrMap-to-ishae f (λ b → ∃-recursion (isContr-is-Prop _) (λ a u → pr₂ isContr-iff-is-inhabited-Prop ((a , u) , (Σ-induction λ x p → Σ-induction λ y q → inv (path-space-fib _ _) ((isequiv₁ (f-is-embedding x y) (p ∙ q ⁻¹)) , ((isequiv₃ (f-is-embedding x y) (p ∙ q ⁻¹) ∙ᵣ q) ∙ ∙-assoc _ _ _ ⁻¹ ∙ (p ∙ₗ linv q) ∙ ru p ⁻¹ ))))) (f-is-surjective b))
  

  



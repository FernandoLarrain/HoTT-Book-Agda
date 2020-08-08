{-# OPTIONS --without-K --exact-split --safe #-}

open import Ch1.Type-theory
open import Ch2.Homotopy-type-theory
open import Ch3.Sets-and-logic
open import Ch4.2-Half-adjoint-equivalences
open import Ch4.4-Contractible-fibers

module Ch4.6-Surjections-and-embeddings where

open PropTrunc ⦃ ... ⦄


-- Definition 4.6.1 (Surjections and embeddings)

is-surjective : ⦃ pt : PropTrunc ⦄ {A : 𝓤 ̇} {B : 𝓥 ̇} → (A → B) → 𝓤 ⊔ 𝓥 ̇
is-surjective {A = A} {B = B} f = (b : B) → ∃ a ꞉ A , (f a ≡ b)

is-surjective-is-Prop : ⦃ fe : FunExt ⦄ ⦃ pt : PropTrunc ⦄ {A : 𝓤 ̇} {B : 𝓥 ̇} (f : A → B) → isProp (is-surjective f)
is-surjective-is-Prop f = Π-preserves-Props _ λ y → ∃-is-Prop 

is-embedding : {A : 𝓤 ̇} {B : 𝓥 ̇} → (A → B) → 𝓤 ⊔ 𝓥 ̇
is-embedding {𝓤} {𝓥} {A} {B} f = (x y : A) → isequiv (ap f {x} {y})  

is-injective : {A : 𝓤 ̇} {B : 𝓥 ̇} → (A → B) → 𝓤 ⊔ 𝓥 ̇
is-injective {𝓤} {𝓥} {A} {B} f = (x y : A) → f x ≡ f y → x ≡ y

module _ ⦃ fe : FunExt ⦄ {A : 𝓤 ̇} {B : 𝓥 ̇} where

  is-embedding-is-Prop : (f : A → B) → isProp (is-embedding f)
  is-embedding-is-Prop f = Π-preserves-Props _ λ x → Π-preserves-Props _ λ y → ishae-is-Prop _

  injectivity-in-Set-is-Prop : isSet A → (f : A → B) → isProp (is-injective f)
  injectivity-in-Set-is-Prop A-is-Set f f-is-injective f-is-injective' = funext λ x → funext λ y → funext λ p → A-is-Set _ _ _ _
  
  embedding-of-sets-is-injection : isSet A → isSet B → (f : A → B) → (is-embedding f ≃ is-injective f)
  embedding-of-sets-is-injection A-is-Set B-is-Set f = ⇔-to-≃ (is-embedding-is-Prop _) (injectivity-in-Set-is-Prop A-is-Set _) (sufficiency , necessity)
    where
    sufficiency : is-embedding f → is-injective f
    sufficiency f-is-embedding x y p = ap-f-inv p where
      ap-f-inv = isequiv₁ (f-is-embedding x y)
    necessity : is-injective f → is-embedding f
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

isPropMap-to-is-embedding : {A : 𝓤 ̇} {B : 𝓥 ̇} (f : A → B) → isPropMap f → is-embedding f
isPropMap-to-is-embedding f f-is-Prop x x' = isContrMap-to-ishae _ (λ p → ≃-preserves-Contr (≃-sym (fib-of-ap-is-path-space-fib p)) (pr₁ (Prop-iff-Contr-≡ (fib f (f x'))) (f-is-Prop (f x')) (x , p) (x' , refl (f x')))) 

is-embedding-to-isPropMap : {A : 𝓤 ̇} {B : 𝓥 ̇} (f : A → B) → is-embedding f → isPropMap f
is-embedding-to-isPropMap f f-is-embedding y = pr₂ (Prop-iff-Contr-≡ (fib f y)) (λ w w' → ≃-preserves-Contr (≃-sym (path-space-fib-is-fib-of-ap w w')) (ishae-to-isContrMap _ (f-is-embedding (pr₁ w) (pr₁ w')) _))

is-embedding-≃-isPropMap : ⦃ fe : FunExt ⦄ {A : 𝓤 ̇} {B : 𝓥 ̇} (f : A → B) → is-embedding f ≃ isPropMap f
is-embedding-≃-isPropMap f = ⇔-to-≃ (is-embedding-is-Prop f) (isPropMap-is-Prop f) (is-embedding-to-isPropMap f , isPropMap-to-is-embedding f)  


-- Theorem 4.6.3 / Corollary 4.6.4 (Equivalences are surjective embeddings)

isequiv-≃-is-surjective-embedding : ⦃ fe : FunExt ⦄ ⦃ pt : PropTrunc ⦄ {A : 𝓤 ̇} {B : 𝓥 ̇} (f : A → B) → isequiv f ≃ (is-surjective f × is-embedding f)
isequiv-≃-is-surjective-embedding f = ⇔-to-≃ (ishae-is-Prop _) (×-preserves-Props _ _ (is-surjective-is-Prop _) (is-embedding-is-Prop _)) (sufficiency , necessity) where
  sufficiency :  isequiv f → is-surjective f × is-embedding f
  sufficiency f-is-equiv = (λ b → ∣ (pr₁ (ishae-to-isContrMap _ f-is-equiv b)) ∣) , ap-of-equiv-is-equiv f-is-equiv
  necessity : is-surjective f × is-embedding f → isequiv f
  necessity (f-is-surjective , f-is-embedding) = isContrMap-to-ishae f (λ b → ∃-recursion (isContr-is-Prop _) (λ a u → pr₂ isContr-iff-is-inhabited-Prop ((a , u) , (Σ-induction λ x p → Σ-induction λ y q → inv (path-space-fib _ _) ((isequiv₁ (f-is-embedding x y) (p ∙ q ⁻¹)) , ((isequiv₃ (f-is-embedding x y) (p ∙ q ⁻¹) ∙ᵣ q) ∙ ∙-assoc _ _ _ ⁻¹ ∙ (p ∙ₗ linv q) ∙ ru p ⁻¹ ))))) (f-is-surjective b))
  

  



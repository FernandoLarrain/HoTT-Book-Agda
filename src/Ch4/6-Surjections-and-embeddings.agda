{-# OPTIONS --without-K --exact-split #-}

open import Ch1.Type-theory
open import Ch2.Homotopy-type-theory
open import Ch3.Sets-and-logic
open import Ch4.2-Half-adjoint-equivalences
open import Ch4.4-Contractible-fibers

module Ch4.6-Surjections-and-embeddings where

module surjections (pt : propositional-truncations-exist) where

  open basic-truncation-development pt
  
  -- Definition 4.6.1 (Surjections and embeddings)

  is-surjective : {A : 𝓤 ̇} {B : 𝓥 ̇} → (A → B) → 𝓤 ⊔ 𝓥 ̇
  is-surjective {A = A} {B = B} f = (b : B) → ∃ a ꞉ A , (f a ≡ b)

  is-surjective-is-Prop : {A : 𝓤 ̇} {B : 𝓥 ̇} (f : A → B) → isProp (is-surjective f)
  is-surjective-is-Prop f = Π-preserves-Props _ λ y → ∃-is-Prop 

is-embedding : {A : 𝓤 ̇} {B : 𝓥 ̇} → (A → B) → 𝓤 ⊔ 𝓥 ̇
is-embedding {A = A} f = (x y : A) → isequiv (ap f {x} {y})  

module _ {A : 𝓤 ̇} {B : 𝓥 ̇} where

  is-injective : (A → B) → 𝓤 ⊔ 𝓥 ̇
  is-injective f = (x y : A) → f x ≡ f y → x ≡ y

  is-embedding-is-Prop : (f : A → B) → isProp (is-embedding f)
  is-embedding-is-Prop f = Π-preserves-Props _ λ x → Π-preserves-Props _ λ y → ishae-is-Prop _

  injectivity-in-Set-is-Prop : isSet A → (f : A → B) → isProp (is-injective f)
  injectivity-in-Set-is-Prop A-is-Set f f-is-injective f-is-injective' = funext _ _ λ x → funext _ _ λ y → funext _ _ λ p → A-is-Set _ _ _ _
  
  embedding-of-sets-is-injection : isSet A → isSet B → (f : A → B) → (is-embedding f ≃ is-injective f)
  embedding-of-sets-is-injection A-is-Set B-is-Set f = biimplication-to-≃ _ _ (is-embedding-is-Prop _) (injectivity-in-Set-is-Prop A-is-Set _) sufficiency necessity
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


module isequiv-≃-is-surjective-embedding (pt : propositional-truncations-exist) where 

  open basic-truncation-development pt
  open surjections pt

  -- Theorem 4.6.3 / Corollary 4.6.4 (Equivalences are surjective embeddings)

  isequiv-≃-is-surjective-embedding : {A : 𝓤 ̇} {B : 𝓥 ̇} (f : A → B) → isequiv f ≃ (is-surjective f × is-embedding f)
  isequiv-≃-is-surjective-embedding f = biimplication-to-≃ _ _ (ishae-is-Prop _) (×-preserves-Props _ _ (is-surjective-is-Prop _) (is-embedding-is-Prop _)) sufficiency necessity where
    sufficiency :  isequiv f → is-surjective f × is-embedding f
    sufficiency f-is-equiv = (λ b → ∣ (pr₁ (f-is-Contr-Map b)) ∣) , ap-of-equiv-is-equiv _ _ _ f-is-equiv
      where
      f-is-Contr-Map = isequiv₁ (pr₂ (isContrMap-≃-ishae f)) f-is-equiv
    necessity : is-surjective f × is-embedding f → isequiv f
    necessity (f-is-surjective , f-is-embedding) = pr₁ (isContrMap-≃-ishae f) (λ b → ∃-recursion (isContr-is-Prop _) (λ a u → pr₂ (isContr-iff-is-inhabited-Prop _) ((a , u) , (Σ-induction λ x p → Σ-induction λ y q → isequiv₁ (pr₂ (path-space-fib _ _)) ((isequiv₁ (f-is-embedding x y) (p ∙ q ⁻¹)) , (isequiv₃ (f-is-embedding x y) (p ∙ q ⁻¹) ∙ᵣ q ∙ ∙-assoc _ _ _ ⁻¹ ∙ (p ∙ₗ linv q) ∙ ru p ⁻¹ ))))) (f-is-surjective b))
  
  
  



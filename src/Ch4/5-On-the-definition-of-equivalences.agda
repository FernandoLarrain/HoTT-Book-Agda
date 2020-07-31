{-# OPTIONS --without-K --exact-split --safe #-}

open import Ch1.Type-theory
open import Ch2.Homotopy-type-theory
open import Ch3.Sets-and-logic
open import Ch4.2-Half-adjoint-equivalences
open import Ch4.3-Bi-invertible-maps
open import Ch4.4-Contractible-fibers

module Ch4.5-On-the-definition-of-equivalences where

{- Note: Up to this point, the official definition of equivalence is bi-invertible maps. From now on , it is half-adjoint equivalences. The code works with both definitions until Ch4.4-Contractible-fibers. -}

-- ishae contains the most directly useful data, as can be seen from the following results, which extend exercise 2.17.

module _ ⦃ fe : FunExt ⦄ where

  Π-preserves-base-≃ : {A : 𝓤 ̇} {B : 𝓥 ̇} (P : B → 𝓦 ̇) (e : A ≃ B) → Π (P ∘ pr₁ e) ≃ Π P
  Π-preserves-base-≃ P (f , g , η , ε , τ) =
    (λ h b → transport P (ε b) (h (g b))) ,
    (qinv-to-ishae (
      (λ k a → k (f a)) ,
      (λ k → funext (λ b → apd k (ε b))) ,
      λ h → funext (λ a → ap (λ - → transport P - (h (g (f a)))) (τ a ⁻¹)∙ (transport-∘ P f (η a) (h (g (f a))) ⁻¹ ∙ apd h (η a)))
      )
    )

  Π-preserves-≃ : {A : 𝓤 ̇} {B : 𝓥 ̇} (P : A → 𝓦 ̇) (Q : B → 𝓣 ̇) (e : A ≃ B) → ((a : A) → P a ≃ Q (pr₁ e a)) → Π P ≃ Π Q
  Π-preserves-≃ P Q e t = Π-preserves-family-≃ t ● Π-preserves-base-≃ Q e  

  Π-preserves-base-≃' : {A : 𝓤 ̇} {B : 𝓥 ̇} (P : A → 𝓦 ̇) (e : A ≃ B) → Π P ≃ Π (P ∘ inv e)
  Π-preserves-base-≃' P e = ≃-sym (Π-preserves-base-≃ P (≃-sym e))

  Π-preserves-≃' : {A : 𝓤 ̇} {B : 𝓥 ̇} (P : A → 𝓦 ̇) (Q : B → 𝓣 ̇) (e : A ≃ B) → ((b : B) → P (inv e b) ≃ Q b) → Π P ≃ Π Q
  Π-preserves-≃' P Q e t = Π-preserves-base-≃' P e ● Π-preserves-family-≃ t

Σ-preserves-base-≃ : {A : 𝓤 ̇} {B : 𝓥 ̇} (P : B → 𝓦 ̇) (e : A ≃ B) → (Σ (P ∘ (pr₁ e)) ≃ Σ P) 
Σ-preserves-base-≃ P (f , g , η , ε , τ) =
  Σ-induction (λ a y → (f a) , y) ,
  (qinv-to-ishae (
    Σ-induction (λ b y → (g b) , (transport P (ε b ⁻¹) y)) ,
    Σ-induction (λ b y → dpair-≡ (ε b , (transport-∙ P (ε b ⁻¹) (ε b) y ∙ ap (λ - → transport P - y) (linv (ε b))))) ,
    Σ-induction (λ a y → dpair-≡ (η a , (transport-∘ P f (η a) _ ∙ (transport-∙ P (ε (f a) ⁻¹) (ap f (η a)) y ∙ ap (λ - → transport P - y) ((ε (f a) ⁻¹ ∙ₗ τ a) ∙ linv (ε (f a)))))))
    )
  )

Σ-preserves-≃ : {A : 𝓤 ̇} {B : 𝓥 ̇} (P : A → 𝓦 ̇) (Q : B → 𝓣 ̇) (e : A ≃ B) → ((a : A) → P a ≃ Q (pr₁ e a)) → Σ P ≃ Σ Q
Σ-preserves-≃ P Q e t = Σ-preserves-family-≃ t ● Σ-preserves-base-≃ Q e 

Σ-preserves-base-≃' : {A : 𝓤 ̇} {B : 𝓥 ̇} (P : A → 𝓦 ̇) (e : A ≃ B) → Σ P ≃ Σ (P ∘ inv e)
Σ-preserves-base-≃' P e = ≃-sym (Σ-preserves-base-≃ P (≃-sym e)) 

Σ-preserves-≃' : {A : 𝓤 ̇} {B : 𝓥 ̇} (P : A → 𝓦 ̇) (Q : B → 𝓣 ̇) (e : A ≃ B) → ((b : B) → P (inv e b) ≃ Q b) → Σ P ≃ Σ Q
Σ-preserves-≃' P Q e t = Σ-preserves-base-≃' P e ● Σ-preserves-family-≃ t

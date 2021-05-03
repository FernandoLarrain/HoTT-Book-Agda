{-# OPTIONS --without-K --exact-split --safe #-}

open import Ch1.Type-theory
open import Ch2.Homotopy-type-theory
open import Ch3.Sets-and-logic
open import Ch4.Equivalences

module Thesis.Z-Algebras where


-- I. The Category of ℤ-Algebras

-- Objects

AlgStr : 𝓤 ̇ → 𝓤 ̇
AlgStr A = A × (Σ s ꞉ (A → A) , ishae s)

Alg : (𝓤 : Universe) → 𝓤 ⁺ ̇
Alg 𝓤 = Σ A ꞉ (𝓤 ̇) , AlgStr A

-- Morphisms

HomStr : (A : Alg 𝓤) (B : Alg 𝓥) → (pr₁ A → pr₁ B) → 𝓤 ⊔ 𝓥 ̇
HomStr (A , a₀ , s , i) (B , b₀ , t , j) f = (f a₀ ≡ b₀) × (f ∘ s ∼ t ∘ f)

Hom : Alg 𝓤 → Alg 𝓥 → 𝓤 ⊔ 𝓥 ̇
Hom A B = Σ f ꞉ (pr₁ A → pr₁ B) , HomStr A B f 

-- Composition

comp : (A : Alg 𝓤) (B : Alg 𝓥) (C : Alg 𝓦) → Hom B C → Hom A B → Hom A C
comp A B C (g , g₀ , g-s) (f , f₀ , f-s) = g ∘ f , (ap g f₀ ∙ g₀) , λ a → ap g (f-s a) ∙ g-s (f a)

-- Identity

algid : (A : Alg 𝓤) → Hom A A
algid A = id , refl _ , hrefl _


-- II. Fibered ℤ-Algebras and their Sections

-- Fibered Algebras

FibAlgStr : (A : Alg 𝓤) → (pr₁ A → 𝓥 ̇) → 𝓤 ⊔ 𝓥 ̇
FibAlgStr (A , a₀ , s , i) E = E a₀ × (Σ s' ꞉ ((a : A) → E a → E (s a)) , ((a : A) → ishae (s' a)))

FibAlg : (𝓥 : Universe) → Alg 𝓤 → 𝓤 ⊔ 𝓥 ⁺ ̇
FibAlg 𝓥 A = Σ E ꞉ (pr₁ A → 𝓥 ̇) , FibAlgStr A E

-- Associated algebra on total space

TotAlg : ⦃ fe : FunExt ⦄ (A : Alg 𝓤) → FibAlg 𝓥 A → Alg (𝓤 ⊔ 𝓥)
TotAlg (A , a₀ , s , i) (E , e₀ , s' , j) = (Σ E) , (a₀ , e₀) , total↓ E s s' , pr₁ (fiberwise-≃-iff-total↓-≃ s E E i s') j

-- TotAlg (A , a₀ , s , i) (E , e₀ , s' , j) = (Σ E) , (a₀ , e₀) , total↓ E s s' , pr₂ (Σ-preserves-≃ E E (s , i) (λ a → s' a , j a))

-- Projection of associated algebra is a morphism

π₁ : ⦃ fe : FunExt ⦄ (A : Alg 𝓤) (E : FibAlg 𝓥 A) → Hom (TotAlg A E) A
π₁ (A , a₀ , s , i) (E , e₀ , s' , j) = pr₁ , refl a₀ , hrefl (s ∘ pr₁)

-- Fibered algebra sections

AlgSecStr : (A : Alg 𝓤) (E : FibAlg 𝓥 A) → ((a : pr₁ A) → (pr₁ E) a) → 𝓤 ⊔ 𝓥 ̇
AlgSecStr (A , a₀ , s , i) (E , e₀ , s' , j) f = (f a₀ ≡ e₀) × ((a : A) → f (s a) ≡ s' a (f a))

AlgSec : (A : Alg 𝓤) → FibAlg 𝓥 A → 𝓤 ⊔ 𝓥 ̇
AlgSec A E = Σ f ꞉ Π (pr₁ E) , AlgSecStr A E f 

-- Section induces morphism into associated algebra

Sec-to-Hom : ⦃ fe : FunExt ⦄ (A : Alg 𝓤) (E : FibAlg 𝓥 A) → AlgSec A E → Hom A (TotAlg A E)
Sec-to-Hom (A , a₀ , s , i) (E , e₀ , s' , j) (f , f₀ , f-s) = (λ a → a , f a) , dpair-≡ (refl a₀ , f₀) , λ a → dpair-≡ (refl (s a) , f-s a)

-- Fibered algebra induced by a constant algebra

ConstFibAlg : (A : Alg 𝓤) (B : Alg 𝓥) → FibAlg 𝓥 A
ConstFibAlg {𝓤} {𝓥} (A , a₀ , s , i) (B , b₀ , s'  , j) = (λ a → B) , b₀ , (λ a b → s' b) , (λ a → j)

_ : (A : Alg 𝓤) (B : Alg 𝓥) → AlgSec A (ConstFibAlg A B) ≡ Hom A B
_ = λ A B → refl _

{-# OPTIONS --without-K --exact-split --safe #-}

open import Ch1.3-Universes-and-families
open import Ch1.2-Function-types
open import Ch1.6-Dependent-pair-types

module Ch1.5-Product-types where


-- Nullary product

data 𝟙 : 𝓤₀ ̇  where
 ⋆ : 𝟙

𝟙-induction : (A : 𝟙 → 𝓤 ̇) → A ⋆ → (x : 𝟙) → A x
𝟙-induction A a ⋆ = a

𝟙-recursion : (B : 𝓤 ̇) → B → 𝟙 → B
𝟙-recursion B b x = 𝟙-induction (λ _ → B) b x

!𝟙 : {X : 𝓤 ̇} → X → 𝟙
!𝟙 x = ⋆


-- Binary product

_×_ : 𝓤 ̇ → 𝓥 ̇ → 𝓤 ⊔ 𝓥 ̇
X × Y = Σ x ꞉ X , Y

infixr 30 _×_ 

×-map : {A : 𝓤 ̇} {B : 𝓥 ̇} {A' : 𝓦 ̇} {B' : 𝓣 ̇} → (A → B) → (A' → B') → A × A' → B × B'
×-map f g = pair (f ∘ pr₁ , g ∘ pr₂)

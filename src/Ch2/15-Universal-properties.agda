{-# OPTIONS --without-K --exact-split --safe #-}

open import Ch1.Type-theory
open import Ch2.1-Types-are-higher-groupoids
open import Ch2.4-Homotopies-and-equivalences
open import Ch2.6-Cartesian-product-types
open import Ch2.7-Σ-types
open import Ch2.9-Π-types-and-funext

module Ch2.15-Universal-properties where

module _ ⦃ fe : FunExt ⦄ where

  -- Theorem 2.15.2 (Universal mapping property (UMP) of product of types).

  ×-UMP : (X : 𝓤 ̇) (A : 𝓥 ̇) (B : 𝓦 ̇) → isequiv {_} {_} {X → A × B} {(X → A) × (X → B)} ⟨ pr₁ ∘_ , pr₂ ∘_ ⟩ 
  ×-UMP X A B = qinv-to-isequiv (inverse , (α , β)) where
    inverse : (X → A) × (X → B) → X → A × B
    inverse = Σ-induction ⟨_,_⟩
    α : (λ x → (pr₁ ∘ inverse x) , (pr₂ ∘ inverse x)) ∼ (λ x → x)
    α (g , h) = refl _
    β : (λ x → inverse ((pr₁ ∘ x) , (pr₂ ∘ x))) ∼ (λ x → x)
    β f = funext λ x → ×-η (f x) ⁻¹


  -- Theorem 2.15.5 (UMP of product of type families).

  dep-×-UMP : (X : 𝓤 ̇) (A : X → 𝓥 ̇) (B : X → 𝓦 ̇) → isequiv {_} {_} {(x : X) → A x × B x} {(Π A) × (Π B)} (λ f → (λ x → pr₁ (f x)), (λ x → pr₂ (f x)))
  dep-×-UMP X A B = qinv-to-isequiv (inverse , (α , β)) where
    inverse : (Π A) × (Π B) → (x : X) → A x × B x
    inverse (g , h) x = (g x) , (h x)
    α : (λ x → (λ x₁ → pr₁ (inverse x x₁)) , (λ x₁ → pr₂ (inverse x x₁))) ∼ (λ x → x)
    α (g , h) = refl _
    β : (λ x → inverse ((λ x₁ → pr₁ (x x₁)) , (λ x₁ → pr₂ (x x₁)))) ∼ (λ x → x)
    β f = funext λ x → Σ-η (f x) ⁻¹


  -- Theorem 2.15.7 (UMP of sum over type families ("Axiom of Choice")).

  dep-Σ-UMP : (X : 𝓤 ̇) (A : X → 𝓥 ̇) (P : (x : X) → A x → 𝓦 ̇) → isequiv {_} {_} {(x : X) → Σ (P x)} {Σ g ꞉ Π A , ((x : X) → P x (g x))} (λ f → (λ x → pr₁ (f x)) , (λ x → pr₂ (f x)))
  dep-Σ-UMP X A P = qinv-to-isequiv (inverse , (α , β)) where
    inverse : Σ g ꞉ Π A , ((x : X) → P x (g x)) → (x : X) → Σ (P x)
    inverse (g , h) x = (g x) , (h x)
    α : (λ x → (λ x₁ → pr₁ (inverse x x₁)) , (λ x₁ → pr₂ (inverse x x₁))) ∼ (λ x → x)
    α (g , h) = refl _
    β : (λ x → inverse ((λ x₁ → pr₁ (x x₁)) , (λ x₁ → pr₂ (x x₁)))) ∼ (λ x → x)
    β f = funext λ x → Σ-η (f x) ⁻¹


-- (Generalized) Cartesian-Closure Adjunction

GCCAdj : (A : 𝓤 ̇) (B : A → 𝓥 ̇) (C : Σ B → 𝓦 ̇) → ((w : Σ B) → C w) ≃ ((x : A) → (y : B x) → C (x , y))
GCCAdj A B C = curry , qinv-to-isequiv (
  Σ-induction ,
  (λ f → refl _) ,
  λ f → refl _
  )


-- Definition (Pullback)

pb : {A : 𝓤 ̇} {B : 𝓥 ̇} {C : 𝓦 ̇} → (A → C) → (B → C) → (𝓤 ⊔ 𝓥 ⊔ 𝓦) ̇
pb {𝓤} {𝓥} {𝓦} {A} {B} {C} f g = Σ (λ a → Σ (λ b → f a ≡ g b))

module pb {A : 𝓤 ̇} {B : 𝓥 ̇} {C : 𝓦 ̇} (f : A → C) (g : B → C) where

  pb₁ : pb f g → A
  pb₁ (a , b , p) = a

  pb₂ : pb f g → B
  pb₂ (a , b , p) = b

  pb-comm : f ∘ pb₁ ∼ g ∘ pb₂
  pb-comm (a , b , p) = p

open pb public

_×⟨_⟩_ : (A : 𝓤 ̇) (C : 𝓦 ̇) (B : 𝓥 ̇) → (A → C) → (B → C) → (𝓤 ⊔ 𝓥 ⊔ 𝓦) ̇
(A ×⟨ C ⟩ B) f g = pb f g


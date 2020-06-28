{-# OPTIONS --without-K --exact-split #-}

open import Ch1.Type-theory
open import Ch2.1-Types-are-higher-groupoids
open import Ch2.4-Homotopies-and-equivalences
open import Ch2.6-Cartesian-product-types
open import Ch2.7-Σ-types
open import Ch2.9-Π-types-and-funext

module Ch2.15-Universal-properties where


-- Theorem 2.15.2 (Universal mapping property (UMP) of product of types).

×-UMP : (X : 𝓤 ̇ ) (A : 𝓥 ̇ ) (B : 𝓦 ̇ ) → isequiv {A = X → A × B} {(X → A) × (X → B)} (λ f → (pr₁ ∘ f) , (pr₂ ∘ f))
×-UMP X A B = qinv-to-isequiv (inv , (α , β)) where
  inv : (X → A) × (X → B) → X → A × B
  inv (g , h) x = (g x) , (h x)
  α : (λ x → (pr₁ ∘ inv x) , (pr₂ ∘ inv x)) ∼ (λ x → x)
  α (g , h) = refl _
  β : (λ x → inv ((pr₁ ∘ x) , (pr₂ ∘ x))) ∼ (λ x → x)
  β f = funext _ _ λ x → ×-η (f x) ⁻¹
  

-- Theorem 2.15.5 (UMP of product of type families).

dep-×-UMP : (X : 𝓤 ̇ ) (A : X → 𝓥 ̇ ) (B : X → 𝓦 ̇ ) → isequiv {A = (x : X) → A x × B x} {(Π A) × (Π B)} (λ f → (λ x → pr₁ (f x)), (λ x → pr₂ (f x)))
dep-×-UMP X A B = qinv-to-isequiv (inv , (α , β)) where
  inv : (Π A) × (Π B) → (x : X) → A x × B x
  inv (g , h) x = (g x) , (h x)
  α : (λ x → (λ x₁ → pr₁ (inv x x₁)) , (λ x₁ → pr₂ (inv x x₁))) ∼ (λ x → x)
  α (g , h) = refl _
  β : (λ x → inv ((λ x₁ → pr₁ (x x₁)) , (λ x₁ → pr₂ (x x₁)))) ∼ (λ x → x)
  β f = funext _ _ λ x → Σ-η (f x) ⁻¹
  

-- Theorem 2.15.7 (UMP of sum over type families ("Axiom of Choice")).

dep-Σ-UMP : (X : 𝓤 ̇ ) (A : X → 𝓥 ̇ ) (P : (x : X) → A x → 𝓦 ̇ ) → isequiv {A = (x : X) → Σ (P x)} {Σ g ꞉ Π A , ((x : X) → P x (g x))} (λ f → (λ x → pr₁ (f x)) , (λ x → pr₂ (f x)))
dep-Σ-UMP X A P = qinv-to-isequiv (inv , (α , β)) where
  inv : Σ g ꞉ Π A , ((x : X) → P x (g x)) → (x : X) → Σ (P x)
  inv (g , h) x = (g x) , (h x)
  α : (λ x → (λ x₁ → pr₁ (inv x x₁)) , (λ x₁ → pr₂ (inv x x₁))) ∼ (λ x → x)
  α (g , h) = refl _
  β : (λ x → inv ((λ x₁ → pr₁ (x x₁)) , (λ x₁ → pr₂ (x x₁)))) ∼ (λ x → x)
  β f = funext _ _ λ x → Σ-η (f x) ⁻¹


-- (Generalized) Cartesian-Closure Adjunction

GCCAdj : (A : 𝓤 ̇) (B : A → 𝓥 ̇) (C : Σ B → 𝓦 ̇) → ((w : Σ B) → C w) ≃ ((x : A) → (y : B x) → C (x , y))
GCCAdj A B C = curry , qinv-to-isequiv (
  Σ-induction ,
  (λ f → refl _) ,
  λ f → refl _
  )


-- Definition (Pullback)

pb : {A : 𝓤 ̇ } {B : 𝓥 ̇ } {C : 𝓦 ̇ } → (A → C) → (B → C) → (𝓤 ⊔ 𝓥 ⊔ 𝓦) ̇
pb {A = A} {B} {C} f g = Σ (λ a → Σ (λ b → f a ≡ g b))


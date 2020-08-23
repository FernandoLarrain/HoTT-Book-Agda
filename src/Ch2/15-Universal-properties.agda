{-# OPTIONS --without-K --exact-split --safe #-}

open import Ch1.Type-theory
open import Ch2.1-Types-are-higher-groupoids
open import Ch2.2-Functions-are-functors
open import Ch2.3-Type-families-are-fibrations
open import Ch2.4-Homotopies-and-equivalences
open import Ch2.6-Cartesian-product-types
open import Ch2.7-Σ-types
open import Ch2.9-Π-types-and-funext

module Ch2.15-Universal-properties where

module _ ⦃ fe : FunExt ⦄ where


  -- Theorem 2.15.2 (Universal mapping property (UMP) of product of types).

  ×-UMP : (X : 𝓤 ̇) (A : 𝓥 ̇) (B : 𝓦 ̇) → isequiv {_} {_} {X → A × B} {(X → A) × (X → B)} split
  ×-UMP X A B = qinv-to-isequiv (pair , hrefl _ , λ f → funext λ x → ×-η (f x) ⁻¹)

  private

    -- Products are unique (using universe polymorphism).

    module ×-UMP-to-≃ (A : 𝓤 ̇) (B : 𝓥 ̇) (P : 𝓦 ̇) (π₁ : P → A) (π₂ : P → B) (i : {𝓣 : Universe} (X : 𝓣 ̇) → isequiv {_} {_} {X → P} {(X → A) × (X → B)} (λ f → π₁ ∘ f , π₂ ∘ f)) where

      -- Notation

      split' : {X : 𝓣 ̇} → (X → P) → (X → A) × (X → B)
      split' f = π₁ ∘ f , π₂ ∘ f

      pair' : {X : 𝓣 ̇} → (X → A) × (X → B) → (X → P)
      pair' {𝓣} {X} = qinv₁ (isequiv-to-qinv (i X))

      -- Relevant quasi-inverses

      q : qinv (λ (f : A × B → P) → π₁ ∘ f , π₂ ∘ f)
      q = isequiv-to-qinv (i (A × B))

      q' : qinv (λ (f : P → P) → π₁ ∘ f , π₂ ∘ f)
      q' = isequiv-to-qinv (i P)

      -- Maps back and forth

      ϕ : P → A × B
      ϕ = pair (π₁ , π₂)

      ψ : A × B → P
      ψ = pair' (pr₁ , pr₂)

      -- Commutativity conditions

      ϕ₁ : pr₁ ∘ ϕ ≡ π₁
      ϕ₁ = refl _

      ϕ₂ : pr₂ ∘ ϕ ≡ π₂
      ϕ₂ = refl _

      ψ₁ : π₁ ∘ ψ ≡ pr₁
      ψ₁ = ap pr₁ (qinv₂ q (pr₁ , pr₂))

      ψ₂ : π₂ ∘ ψ ≡ pr₂
      ψ₂ = ap pr₂ (qinv₂ q (pr₁ , pr₂))

      -- Witnesses of invertibility

      α : ϕ ∘ ψ ∼ 𝑖𝑑 (A × B)
      α = happly (
        ϕ ∘ ψ
          ≡⟨ funext (×-η ∘ (ϕ ∘ ψ)) ⟩
        pair (split (ϕ ∘ ψ))
          ≡⟨ ap pair (qinv₂ q (pr₁ , pr₂)) ⟩ -- (qinv₂ q (pr₁ , pr₂))
        pair (split (𝑖𝑑 (A × B)))
          ≡⟨ refl _ ⟩
        𝑖𝑑 (A × B) ∎
        )

      β : ψ ∘ ϕ ∼ 𝑖𝑑 P
      β = happly (
        ψ ∘ ϕ
          ≡⟨ qinv₃ q' (ψ ∘ ϕ) ⁻¹ ⟩
        pair' (split' (ψ ∘ ϕ))
          ≡⟨ ap pair' (pair-≡ (ap (_∘ ϕ) ψ₁ , ap (_∘ ϕ) ψ₂)) ⟩
        pair'(split' (𝑖𝑑 P))
          ≡⟨ qinv₃ q' (𝑖𝑑 P) ⟩
        𝑖𝑑 P ∎
        )

      -- Equivalence

      equiv : P ≃ A × B
      equiv = ϕ , qinv-to-isequiv (ψ , α , β)


  -- UMP of dependent pair types.

  Σ-UMP : (X : 𝓤 ̇) (A : 𝓥 ̇) (B : A → 𝓦 ̇) → isequiv {_} {_} {X → Σ B} {Σ g ꞉ (X → A) , Π (B ∘ g)} split  
  Σ-UMP X A B = qinv-to-isequiv {_} {_} {X → Σ B} {Σ g ꞉ (X → A) , Π (B ∘ g)} {split} (pair , hrefl _ , λ f → funext λ x → Σ-η (f x) ⁻¹) 


  -- Theorem 2.15.5 (UMP of product of type families).

  dep-×-UMP : (X : 𝓤 ̇) (A : X → 𝓥 ̇) (B : X → 𝓦 ̇) → isequiv {_} {_} {(x : X) → A x × B x} {(Π A) × (Π B)} split
  dep-×-UMP X A B = qinv-to-isequiv (pair , hrefl _ , λ f → funext λ x → ×-η (f x) ⁻¹)


  -- Theorem 2.15.7 (UMP of sum over type families ("Axiom of Choice")).

  dep-Σ-UMP : (X : 𝓤 ̇) (A : X → 𝓥 ̇) (P : (x : X) → A x → 𝓦 ̇) → isequiv {_} {_} {(x : X) → Σ (P x)} {Σ g ꞉ Π A , ((x : X) → P x (g x))} split
  dep-Σ-UMP X A P = qinv-to-isequiv (pair , hrefl _ , λ f → funext λ x → Σ-η (f x) ⁻¹)


-- (Generalized) Cartesian-Closure Adjunction

GCCAdj : (A : 𝓤 ̇) (B : A → 𝓥 ̇) (C : Σ B → 𝓦 ̇) → ((w : Σ B) → C w) ≃ ((x : A) → (y : B x) → C (x , y))
GCCAdj A B C = curry , qinv-to-isequiv (Σ-induction , hrefl _ , hrefl _)


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


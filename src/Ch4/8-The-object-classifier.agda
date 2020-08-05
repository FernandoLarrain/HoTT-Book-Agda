{-# OPTIONS --without-K --exact-split --safe #-}

open import Ch1.Type-theory
open import Ch2.Homotopy-type-theory
open import Ch3.Sets-and-logic
open import Ch4.2-Half-adjoint-equivalences
open import Ch4.7-Closure-properties-of-equivalences

module Ch4.8-The-object-classifier where


-- Lemma 4.8.1 (fibers of pr₁ are values of type family)

fibs-of-pr₁-are-values : {A : 𝓤 ̇} {B : A → 𝓥 ̇} (a : A) → fib {𝓤 ⊔ 𝓥} {𝓤} {Σ B} pr₁ a ≃ B a
fibs-of-pr₁-are-values {𝓤} {𝓥} {A} {B} a =
  fib pr₁ a
    ≃⟨ ≃-sym (Σ-assoc _ _ _) ⟩
  (Σ x ꞉ A , (B x × (x ≡ a)))
    ≃⟨ Σ-preserves-family-≃ (λ x → ×-swap _ _) ⟩
  (Σ x ꞉ A , ((x ≡ a) × B x))
    ≃⟨ (Σ-assoc _ _ _) ⟩
  (Σ w ꞉ (Σ x ꞉ A , x ≡ a) , B (pr₁ w))
    ≃⟨ Σ-over-Contr-base-is-fib _ _ (free-left-endpt-is-Contr _ _) ⟩
  B a ■


-- Lemma 4.8.2 (Domain is sum of fibers)

dom-is-sum-of-fibs : {A : 𝓤 ̇} {B : 𝓥 ̇} (f : A → B) → (Σ b ꞉ B , fib f b) ≃ A
dom-is-sum-of-fibs {𝓤} {𝓥} {A} {B} f = Σ-swap B A (λ b a → f a ≡ b) ● Σ-of-Contr-family-is-base _ _ (λ x → free-right-endpt-is-Contr _ _)


-- Theorem 4.8.3

module thm-4-8-3 ⦃ fe : FunExt ⦄ ⦃ univ : Univalence ⦄ (B : 𝓤 ̇) where

  χ : (Σ A ꞉ 𝓤 ̇ , (A → B)) → B → 𝓤 ̇
  χ (A , f) b = fib f b

  ψ : (B → 𝓤 ̇) → (Σ A ꞉ 𝓤 ̇ , (A → B))
  ψ P = (Σ P) , pr₁

  α : χ ∘ ψ ∼ id
  α P = funext λ b → ua (fibs-of-pr₁-are-values b)

  β : ψ ∘ χ ∼ id
  β (A , f) = let g = pr₂ (ψ (χ (A , f))) in dpair-≡ ((ua (dom-is-sum-of-fibs f)) , (funext (transport-along-ua-is-pre-∘' (dom-is-sum-of-fibs f) g)))

  χ-has-qinv : qinv χ
  χ-has-qinv = ψ , α , β
  
  χ-is-equiv : isequiv χ
  χ-is-equiv = qinv-to-isequiv χ-has-qinv

--open thm-4-8-3 using (χ ; χ-has-qinv ; χ-is-equiv)


-- Theorem 4.8.4 (Object classifier).

module object-classifier ⦃ fe : FunExt ⦄ ⦃ univ : Univalence ⦄ {A B : 𝓤 ̇} (f : A → B) where

  open module M = thm-4-8-3 B using (χ)

  ϑ : A → 𝓤 ⊙
  ϑ a = (fib f (f a)) , (a , (refl (f a)))

  π₁ : 𝓤 ⊙ → 𝓤 ̇
  π₁ = pr₁

  pb-square : comm-sq (χ (A , f)) π₁ A
  pb-square = f , ϑ , hrefl _

  object-≃ : A ≃ (B ×⟨ 𝓤 ̇ ⟩ (𝓤 ⊙)) (χ (A , f)) π₁
  object-≃ =
    A
      ≃⟨ ≃-sym (dom-is-sum-of-fibs f) ⟩
    (Σ b ꞉ B , fib f b)
      ≃⟨ Σ-preserves-family-≃ (λ b → ≃-sym (Σ-over-Contr-base-is-fib _ _ (free-right-endpt-is-Contr _ _))) ⟩
    (Σ b ꞉ B , Σ w ꞉ (Σ X ꞉ 𝓤 ̇ , fib f b ≡ X) , pr₁ w)
      ≃⟨ (Σ-preserves-family-≃ λ b → ≃-sym (Σ-assoc _ _ _)) ⟩
    (Σ b ꞉ B , Σ X ꞉ 𝓤 ̇ , (fib f b ≡ X) × X)
      ≃⟨ (Σ-preserves-family-≃ λ b → Σ-preserves-family-≃ λ X → ×-swap _ _) ⟩
    (Σ b ꞉ B , Σ X ꞉ 𝓤 ̇ , X × (fib f b ≡ X))
      ≃⟨ (Σ-preserves-family-≃ λ b → Σ-assoc _ _ _) ⟩
    (Σ b ꞉ B , Σ Y ꞉ (𝓤 ⊙) , (fib f b ≡ π₁ Y))
      ≃⟨ ≃-refl _ ⟩
    ((B ×⟨ 𝓤 ̇ ⟩ (𝓤 ⊙)) (χ (A , f)) π₁) ■

  _ : (a : A) → pr₁ object-≃ a ≡ f a , (fib f (f a) , a , refl (f a)) , refl (fib f (f a))
  _ = hrefl _

  _ : (ϑ ∼ pb₂ (χ (A , f)) π₁ ∘ pr₁ object-≃) × (f ∼ pb₁ (χ (A , f)) π₁ ∘ pr₁ object-≃)
  _ = (hrefl _) , (hrefl _)
 
  UMP-of-pb-square : (X : 𝓣 ̇) → isequiv {_} {_} {X → A} {comm-sq (χ (A , f)) π₁ X} (λ u → f ∘ u , ϑ ∘ u , hrefl (π₁ ∘ ϑ) ∘ u)
  UMP-of-pb-square X = 2-out-of-3.-∘ (pr₁ object-≃ ∘_) (λ u → pb₁ (χ (A , f)) π₁ ∘ u , pb₂ (χ (A , f)) π₁ ∘ u , pb-comm (χ (A , f)) π₁ ∘ u) (pr₂ (→-preserves-codom-≃ X object-≃)) (pb-UMP (χ (A , f)) π₁ X)


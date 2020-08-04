{-# OPTIONS --without-K --exact-split --safe #-}

open import Ch1.Type-theory
open import Ch2.Homotopy-type-theory
open import Ch3.Sets-and-logic
open import Ch4.2-Half-adjoint-equivalences

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

open thm-4-8-3 using (χ ; χ-has-qinv ; χ-is-equiv)


-- Theorem 4.8.4 (Object classifier).

module object-classifier ⦃ fe : FunExt ⦄ ⦃ univ : Univalence ⦄ {A B : 𝓤 ̇} (f : A → B) where

  ϑ : A → 𝓤 ⊙
  ϑ a = (fib f (f a)) , (a , (refl (f a)))

  object-≃ : A ≃ (B ×⟨ 𝓤 ̇ ⟩ (𝓤 ⊙)) (χ B (A , f)) pr₁
  object-≃ =
    A
      ≃⟨ ≃-sym (dom-is-sum-of-fibs f) ⟩
    (Σ b ꞉ B , fib f b)
      ≃⟨ Σ-preserves-family-≃ (λ b → ≃-sym (Σ-over-Contr-base-is-fib _ _ (free-right-endpt-is-Contr _ _))) ⟩
    (Σ b ꞉ B , Σ w ꞉ (Σ X ꞉ 𝓤 ̇ , fib f b ≡ X) , pr₁ w)
      ≃⟨ {!!} ⟩
    {!!}
      ≃⟨ {!!} ⟩
    {!!}
      ≃⟨ {!!} ⟩
    {!!}

  -- Show equivalence as in the book. Then show that the equivalence commutes with the projections. Show in Ch2.Exercises that this means that A satisfies pb-UMP. 



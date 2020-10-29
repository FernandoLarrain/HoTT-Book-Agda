{-# OPTIONS --without-K --exact-split --rewriting #-}

open import Ch1.Type-theory
open import Ch2.Homotopy-type-theory
open import Ch3.Sets-and-logic
open import Ch4.Equivalences
open import Rewrite

module Ch6.10-Quotients where

module _ {A : 𝓤 ̇} where

  postulate

    -- (i) Type formation rule
  
    Set/ : (A → A → 𝓥 ̇) → 𝓤 ⊔ 𝓥 ̇

  module _ {R : A → A → 𝓥 ̇} where

    postulate

      -- (ii) Constructors

      q[_] : A → Set/ R

      rel-to-≡ : {a b : A} → R a b → q[ a ] ≡ q[ b ]

      Set/-is-Set : isSet (Set/ R)

    module _ {P : Set/ R → 𝓦 ̇} (i : (x : Set/ R) → isSet (P x)) (f : Π (P ∘ q[_])) (resp : (a b : A) (r : R a b) → f a ≡ f b [ P ↓ rel-to-≡ r ]) where

      postulate

        -- (iii) Induction principle

        quot-ind : (x : Set/ R) → P x

        -- (iv) Computation rules

        q[_]-β : (a : A) → quot-ind q[ a ] ↦ f a

        {-# REWRITE q[_]-β #-}


-- Remark 6.10.11 (Definition of ℤ via canonical representatives).

r : ℕ × ℕ → ℕ × ℕ
r (zero , zero) = zero , zero
r (succ m , zero) = succ m , zero
r (zero , succ n) = zero , succ n
r (succ m , succ n) = r (m , n)

ℤᵣ : 𝓤₀ ̇
ℤᵣ = Σ z ꞉ ℕ × ℕ , r z ≡ z

-- Embedding of ℕ in ℤᵣ

nonneg : ℕ → ℤᵣ
nonneg zero = (zero , zero) , refl _
nonneg (succ n) = (succ n , zero) , refl _

nonpos : ℕ → ℤᵣ
nonpos zero = (zero , zero) , refl _
nonpos (succ n) = (zero , succ n) , refl _



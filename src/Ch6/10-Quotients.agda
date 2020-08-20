{-# OPTIONS --without-K --exact-split --safe #-}

open import Ch1.Type-theory
open import Ch2.Homotopy-type-theory
open import Ch3.Sets-and-logic
open import Ch4.Equivalences

module Ch6.10-Quotients where


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



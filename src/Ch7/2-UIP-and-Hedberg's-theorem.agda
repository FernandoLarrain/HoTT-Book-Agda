{-# OPTIONS --without-K --exact-split #-}

open import Ch1.Type-theory
open import Ch2.Homotopy-type-theory
open import Ch3.Sets-and-logic
open import Ch4.Equivalences
open import Ch6.5-Suspensions
open import Ch7.1-Definition-of-n-types

module Ch7.2-UIP-and-Hedberg's-theorem where

-- Theorems 7.2.1-9:

open import Ch7.2-UIP-and-Hedberg's-theorem-safe public

-- Corollary of Theorem 7.2.9.

Tlevel-in-terms-of-Map⊙ : (n : Tlevel) (A : 𝓤 ̇) → is (S n) type A ≃ ((a : A) → isContr (Map⊙ (Sphere⊙ (to-ℕ n)) (A , a)))
Tlevel-in-terms-of-Map⊙ n A = generalized-Axiom-K n A ● Π-preserves-family-≃ (λ a → isContr-preserves-≃ (≃-sym (Sphere-UMP (to-ℕ n) _)))

hub-and-spokes : (n : Tlevel) (A : 𝓤 ̇) → is (S n) type A → (l : Sphere (to-ℕ n) → A) → Σ h ꞉ A , l ∼ (λ x → h)
hub-and-spokes n A i l = h , s where
  m : ℕ
  m = to-ℕ n
  h : A
  h = l (base m)
  cₕ : Map⊙ (Sphere⊙ m) (A , h)
  cₕ = (λ x → h) , refl h
  l' : Map⊙ (Sphere⊙ m) (A , h)
  l' = l , refl h
  contr-loops : isContr (Map⊙ (Sphere⊙ m) (A , h))
  contr-loops = pr₁ (Tlevel-in-terms-of-Map⊙ n A) i h
  s : (x : Sphere m) → l x ≡ h
  s = happly (ap pr₁ (isContr-to-isProp contr-loops l' cₕ))

{-# OPTIONS --without-K --exact-split --rewriting #-}

open import Ch1.Type-theory
open import Ch2.Homotopy-type-theory
open import Ch3.Sets-and-logic
open import Ch4.Equivalences

module Ch6.6-Cell-complexes where

-- The Torus, T².

postulate

  -- (i) Type formation rule

  T² : 𝓤₀ ̇

  -- (ii) Constructors
  
  b : T²
  p q : b ≡ b
  t : p ∙ q ≡ q ∙ p

module _ (P : T² → 𝓤 ̇) (b' : P b) (p' : b' ≡ b' [ P ↓ p ]) (q' : b' ≡ b' [ P ↓ q ]) where

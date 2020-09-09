{-# OPTIONS --without-K --exact-split --rewriting #-}

open import Ch1.Type-theory
open import Ch2.Homotopy-type-theory
open import Ch3.Sets-and-logic
open import Rewrite
open import Ch6.4-Circles-and-spheres-safe

module int-as-HIT.replica where


-- Definition 1.1 (Integers as signed natural numbers).

data ℤω : 𝓤₀ ̇ where
  0ω : ℤω
  strpos : ℕ → ℤω
  strneg : ℕ → ℤω


-- Definition 1.3 (Integers using bi-invertible maps).


-- Check definition of integers

-- Alternative definitions:

-- Free grp on one generator

-- Contractible fibers

-- Loop space of circle

-- Signed nats

-- Successor with contractible fibers

-- Successor with bi-invertible maps

-- Induction pple as recursion + eta

{-# OPTIONS --without-K --exact-split --safe #-}

open import Ch1.3-Universes-and-families
open import Ch1.5-Product-types
open import Ch1.7-Coproduct-types

module Ch1.8-The-type-of-booleans where

𝟚 : 𝓤₀ ̇
𝟚 = 𝟙 + 𝟙

pattern ₀ = inl ⋆
pattern ₁ = inr ⋆

𝟚-induction : (A : 𝟚 → 𝓤 ̇ ) → A ₀ → A ₁ → (n : 𝟚) → A n
𝟚-induction A a₀ a₁ ₀ = a₀
𝟚-induction A a₀ a₁ ₁ = a₁

𝟚-recursion : (B : 𝓤 ̇) → B → B → 𝟚 → B
𝟚-recursion B b₀ b₁ ₀ = b₀
𝟚-recursion B b₀ b₁ ₁ = b₁

{-# OPTIONS --without-K --exact-split --safe #-}

open import Ch1.3-Universes-and-families
open import Ch1.7-Coproduct-types

module Ch1.11-Propositions-as-types where

is-empty : 𝓤 ̇  → 𝓤 ̇
is-empty X = X → 𝟘

¬ : 𝓤 ̇  → 𝓤 ̇
¬ X = X → 𝟘




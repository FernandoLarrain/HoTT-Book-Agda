{-# OPTIONS --without-K --exact-split --safe #-}

open import Ch1.3-Universes-and-families

module Ch1.2-Function-types where


-- Identity function

id : {X : 𝓤 ̇} → X → X
id x = x

𝑖𝑑 : (X : 𝓤 ̇) → X → X
𝑖𝑑 X = id

-- Constant function

const : (X : 𝓤 ̇) {Y : 𝓥 ̇} → Y → X → Y
const X y = λ x → y


-- Function composition

_∘_ : {X : 𝓤 ̇} {Y : 𝓥 ̇} {Z : Y → 𝓦 ̇} → ((y : Y) → Z y) → (f : X → Y)
 → (x : X) → Z (f x)
g ∘ f = λ x → g (f x)

infixl 70 _∘_


-- Domain and codomain of a function

domain : {X : 𝓤 ̇} {Y : 𝓥 ̇} → (X → Y) → 𝓤 ̇
domain {𝓤} {𝓥} {X} {Y} f = X

codomain : {X : 𝓤 ̇} {Y : 𝓥 ̇} → (X → Y) → 𝓥 ̇
codomain {𝓤} {𝓥} {X} {Y} f = Y



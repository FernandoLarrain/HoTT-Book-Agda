{-# OPTIONS --without-K --exact-split --safe #-}

open import Ch1.3-Universes-and-families
open import Ch1.2-Function-types

module Ch1.7-Coproduct-types where


-- Nullary coproduct

data 𝟘 : 𝓤₀ ̇  where

𝟘-induction : (A : 𝟘 → 𝓤 ̇) → (x : 𝟘) → A x
𝟘-induction A ()

𝟘-recursion : (B : 𝓤 ̇) → 𝟘 → B
𝟘-recursion B b = 𝟘-induction (λ _ → B) b

!𝟘 : (A : 𝓤 ̇) → 𝟘 → A
!𝟘 = 𝟘-recursion


-- Binary coproduct

data _+_ {𝓤 𝓥} (X : 𝓤 ̇) (Y : 𝓥 ̇) : 𝓤 ⊔ 𝓥 ̇  where
 inl : X → X + Y
 inr : Y → X + Y

infixl 20 _+_

+-induction : {X : 𝓤 ̇} {Y : 𝓥 ̇} (A : X + Y → 𝓦 ̇) → ((x : X) → A (inl x))
 → ((y : Y) → A (inr y)) → (z : X + Y) → A z
+-induction A f g (inl x) = f x
+-induction A f g (inr y) = g y

+-recursion : {X : 𝓤 ̇} {Y : 𝓥 ̇} {A : 𝓦 ̇} → (X → A) → (Y → A) → X + Y → A
+-recursion {𝓤} {𝓥} {𝓦} {X} {Y} {A} = +-induction (λ _ → A)

syntax +-recursion f g = [ f , g ]

+-map : {A : 𝓤 ̇} {B : 𝓥 ̇} {A' : 𝓦 ̇} {B' : 𝓣 ̇} → (A → B) → (A' → B') → A + A' → B + B'
+-map f g = [ inl ∘ f , inr ∘ g ] 

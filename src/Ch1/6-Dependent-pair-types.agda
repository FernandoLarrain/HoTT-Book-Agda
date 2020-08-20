{-# OPTIONS --without-K --exact-split --safe #-}

open import Ch1.3-Universes-and-families
open import Ch1.2-Function-types
open import Ch1.4-Dependent-function-types

module Ch1.6-Dependent-pair-types where


-- Dependent-pair type

record Σ {𝓤 𝓥} {X : 𝓤 ̇} (Y : X → 𝓥 ̇) : 𝓤 ⊔ 𝓥 ̇  where
  constructor
    _,_
  field
    fst : X
    snd : Y fst

infixr 50 _,_

open Σ public

pr₁ : {X : 𝓤 ̇} {Y : X → 𝓥 ̇} → Σ Y → X
pr₁ (x , y) = x

pr₂ : {X : 𝓤 ̇} {Y : X → 𝓥 ̇} → (z : Σ Y) → Y (pr₁ z)
pr₂ (x , y) = y

-Σ : {𝓤 𝓥 : Universe} (X : 𝓤 ̇) (Y : X → 𝓥 ̇) → 𝓤 ⊔ 𝓥 ̇
-Σ X Y = Σ Y

infixr -1 -Σ

syntax -Σ A (λ x → b) = Σ x ꞉ A , b  -- Note: this colon is typed by typing "\:" and then selecting the fourth alternative

Σ-induction : {X : 𝓤 ̇} {Y : X → 𝓥 ̇} {A : Σ Y → 𝓦 ̇} → ((x : X) (y : Y x) → A (x , y)) → (z : Σ Y) → A z
Σ-induction g (x , y) = g x y

curry : {X : 𝓤 ̇} {Y : X → 𝓥 ̇} {A : Σ Y → 𝓦 ̇} → ((z : Σ Y) → A z)
 → ((x : X) (y : Y x) → A (x , y))
curry f x y = f (x , y)

pair : {X : 𝓤 ̇} {A : X → 𝓥 ̇} {P : (x : X) → A x → 𝓦 ̇} → (Σ f ꞉ Π A , ((x : X) → P x (f x))) → (x : X) → Σ (P x)
pair (f , g) x = f x , g x

split : {X : 𝓤 ̇} {A : X → 𝓥 ̇} {P : (x : X) → A x → 𝓦 ̇} → ((x : X) → Σ (P x)) → Σ f ꞉ Π A , ((x : X) → P x (f x))
split h = (λ x → pr₁ (h x)) , (λ x → pr₂ (h x))

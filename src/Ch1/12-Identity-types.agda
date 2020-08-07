{-# OPTIONS --without-K --exact-split --safe #-}

open import Ch1.3-Universes-and-families
open import Ch1.11-Propositions-as-types

module Ch1.12-Identity-types where


-- Identity type

data Id {𝓤} (X : 𝓤 ̇) : X → X → 𝓤 ̇  where
 refl : (x : X) → Id X x x

infix 0 Id

{-# BUILTIN EQUALITY Id #-}

_≡_ : {X : 𝓤 ̇} → X → X → 𝓤 ̇
x ≡ y = Id _ x y

infix 0 _≡_


-- Path induction

𝕁 : (X : 𝓤 ̇) (A : (x y : X) → x ≡ y → 𝓥 ̇) → ((z : X) → A z z (refl z)) →
 (x y : X) (p : x ≡ y) → A x y p
𝕁 X A f x x (refl x) = f x


-- Based path induction

ℍ : {X : 𝓤 ̇} (x : X) (B : (y : X) → x ≡ y → 𝓥 ̇) → B x (refl x) →
 (y : X) (p : x ≡ y) → B y p
ℍ x B b x (refl x) = b


-- Equivalence of path induction and based path induction

𝕁' : (X : 𝓤 ̇) (A : (x y : X) → x ≡ y → 𝓥 ̇) → ((z : X) → A z z (refl z)) →
 (x y : X) (p : x ≡ y) → A x y p
𝕁' X A f x = ℍ x (A x) (f x)

ℍ' : {X : 𝓤 ̇ } (x : X) (B : (y : X) → x ≡ y → 𝓥 ̇) → B x (refl x) →
 (y : X) (p : x ≡ y) → B y p
ℍ' {𝓤} {𝓥} {X} x B b y p =
  let D : (x y : X) → x ≡ y → 𝓤 ⊔ 𝓥 ⁺ ̇
      D x y p = (C : (z : X) → x ≡ z → 𝓥 ̇) → C x (refl x) → C y p 
  in 𝕁 X D (λ z C c → c) x y p B b


-- Disequality

_≢_ : {X : 𝓤 ̇} → X → X → 𝓤 ̇
x ≢ y = ¬ (x ≡ y)

infix 0 _≢_



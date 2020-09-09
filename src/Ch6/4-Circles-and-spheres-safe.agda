{-# OPTIONS --without-K --exact-split --safe #-}

open import Ch1.Type-theory
open import Ch2.Homotopy-type-theory
open import Ch3.Sets-and-logic
open import Ch4.Equivalences

module Ch6.4-Circles-and-spheres-safe where


-- Lemma 6.4.4 (Action on 2-paths).

ap² : {A : 𝓤 ̇ } {B : 𝓥 ̇ } (f : A → B) {x y : A} {p q : x ≡ y} → p ≡ q → ap f p ≡ ap f q
ap² f (refl p) = refl (ap f p)


-- Lemma 6.4.5 (Two-dimensional transport).

transport² : {A : 𝓤 ̇ } (P : A → 𝓥 ̇) {x y : A} {p q : x ≡ y} → p ≡ q → (u : P x) → transport P p u ≡ transport P q u
transport² P (refl p) u = refl (transport P p u)


-- Lemma (transport² in constant family).

transport²const : {A : 𝓤 ̇} (B : 𝓥 ̇) {x y : A} {p q : x ≡ y} (r : p ≡ q) (b : B) → transport² (λ a → B) r b ≡ transportconst B p b ∙ transportconst B q b ⁻¹
transport²const B (refl (refl x)) b = refl _


-- Definition of the type of dependent 2-paths.

PathOver² : {A : 𝓤 ̇} (P : A → 𝓥 ̇) {x y : A} {p q : x ≡ y} (r : p ≡ q) {u : P x} {v : P y} (h : u ≡ v [ P ↓ p ]) (k : u ≡ v [ P ↓ q ]) → 𝓥 ̇
PathOver² P r {u} h k = h ≡ transport² P r u ∙ k

infix 0 PathOver²

syntax PathOver² P r h k = h ≡ k [ P ⇊ r ]


-- Lemma 6.4.6 (Dependent action on 2-paths).

apd² : {A : 𝓤 ̇} {P : A → 𝓥 ̇} {x y : A} {p q : x ≡ y} (f : (x : A) → P x) (r : p ≡ q) → apd f p ≡ apd f q [ P ⇊ r ]
apd² f (refl (refl x)) = refl (refl (f x))


-- Lemma (apd² "reduces" to ap² when family is constant).

apd²-const : {A : 𝓤 ̇} (B : 𝓥 ̇) {x y : A} {p q : x ≡ y} (f : A → B) (r : p ≡ q) → apd² f r ≡ apdconst B f p ∙ (transportconst B p (f x) ∙ₗ (ap² f r ∙ apdconst' B f q)) ∙ ∙-assoc _ _ _ ∙ (transport²const B r (f x) ⁻¹ ∙ᵣ apd f q)
apd²-const B {x} {.x} {.(refl x)} {.(refl x)} f (refl (refl x)) = refl _

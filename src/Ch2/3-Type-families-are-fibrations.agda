{-# OPTIONS --without-K --exact-split --safe #-}

open import Ch1.Type-theory
open import Ch2.1-Types-are-higher-groupoids
open import Ch2.2-Functions-are-functors

module Ch2.3-Type-families-are-fibrations where


-- Lemma 3.2.1 (Transport).

transport : {X : 𝓤 ̇ } (A : X → 𝓥 ̇) {x y : X} → x ≡ y → A x → A y
transport A (refl x) = 𝑖𝑑 (A x)


-- Lemma 2.3.2 (Path lifting property).

plift : {A : 𝓤 ̇ } {P : A → 𝓥 ̇ } {x y : A} (u : P x) (p : x ≡ y) → x , u ≡ y , transport P p u
plift u (refl x) = refl (x , u)


-- Lemma 2.3.4 (Dependent action on paths).

apd : {A : 𝓤 ̇ } {x y : A} {P : A → 𝓥 ̇ } (f : (x : A) → P x) (p : x ≡ y) → transport P p (f x) ≡ f y
apd f (refl x) = refl (f x)


-- Lemma 2.3.5 (Transport in constant family).

transportconst : {A : 𝓤 ̇ } (B : 𝓥 ̇ ) {x y : A} (p : x ≡ y) (b : B) → transport (λ (x : A) → B) p b ≡ b
transportconst B (refl x) b = refl b


-- Lemma 2.3.8 (apd reduces to ap when family is constant)

apd-const : {A : 𝓤 ̇ } (B : 𝓥 ̇ ) {x y : A} (f : A → B) (p : x ≡ y) → apd f p ≡ transportconst B p (f x) ∙ ap f p
apd-const B f (refl x) = refl (refl (f x))

apd-const' : {A : 𝓤 ̇ } (B : 𝓥 ̇ ) {x y : A} (f : A → B) (p : x ≡ y) → ap f p ≡ transportconst B p (f x) ⁻¹ ∙ apd f p
apd-const' B f (refl x) = refl (refl (f x))


-- Lemma 2.3.9 (Composition of transports is transport along concatenation).

transport-∙ : {A : 𝓤 ̇ } (P : A → 𝓥 ̇ ) {x y z : A} (p : x ≡ y) (q : y ≡ z) (u : P x) → transport P q (transport P p u) ≡ transport P (p ∙ q) u
transport-∙ P (refl x) (refl .x) u = refl u


-- Lemma 2.3.10 (Transport: change of base).

transport-∘ : {A : 𝓤 ̇ } {B : 𝓥 ̇ } (P : B → 𝓦 ̇ ) (f : A → B) {x y : A} (p : x ≡ y) (u : P (f x)) → transport (P ∘ f) p u ≡ transport P (ap f p) u
transport-∘ P f (refl x) u = refl u


-- Lemma 2.3.11 (Transport: family of functions).

transport-fun-family : {A : 𝓤 ̇ } (P : A → 𝓥 ̇) (Q : A → 𝓦 ̇) (f : (x : A) → P x → Q x) (x y : A) (p : x ≡ y) (u : P x) → transport Q p (f x u) ≡ f y (transport P p u)
transport-fun-family P Q f x .x (refl .x) u = refl (f x u)


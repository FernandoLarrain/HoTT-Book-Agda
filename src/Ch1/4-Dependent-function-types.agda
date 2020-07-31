{-# OPTIONS --without-K --exact-split --safe #-}

open import Ch1.3-Universes-and-families

module Ch1.4-Dependent-function-types where


-- Dependent function types

Π : {X : 𝓤 ̇ } (A : X → 𝓥 ̇) → 𝓤 ⊔ 𝓥 ̇
Π {𝓤} {𝓥} {X} A = (x : X) → A x

-Π : {𝓤 𝓥 : Universe} (X : 𝓤 ̇) (Y : X → 𝓥 ̇) → 𝓤 ⊔ 𝓥 ̇
-Π X Y = Π Y

infixr -1 -Π

syntax -Π A (λ x → b) = Π x ꞉ A , b


-- Dependent swap

swap : {A : 𝓤 ̇} {B : 𝓥 ̇} {C : A → B → 𝓦 ̇} → ((a' : A) → (b' : B) → C a' b') → (b : B) → (a : A) → C a b
swap f b a = f a b


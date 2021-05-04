{-# OPTIONS --without-K --exact-split --safe #-}

open import Ch1.Type-theory
open import Ch2.Homotopy-type-theory

module Ch3.4-Classical-vs-intuitionistic-logic where


-- Definition 3.4.3 (Decidability).

is-decidable : 𝓤 ̇  → 𝓤 ̇
is-decidable A = A + (¬ A)

decidable-family : {A : 𝓤 ̇ } (B : A → 𝓥 ̇ ) → (𝓤 ⊔ 𝓥) ̇
decidable-family {𝓤} {𝓥} {A} B = (a : A) → is-decidable (B a)

decidable-equality : 𝓤 ̇  → 𝓤 ̇
decidable-equality A = (x y : A) → is-decidable (x ≡ y)

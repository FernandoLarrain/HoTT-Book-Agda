{-# OPTIONS --without-K --exact-split #-}

open import Ch1.Type-theory
open import Ch2.Homotopy-type-theory
open import Ch3.Sets-and-logic
open import Ch4.2-Half-adjoint-equivalences
open import Ch4.3-Bi-invertible-maps

module Ch4.4-Contractible-fibers where


-- Definition 4.4.1 (Contractible maps).

isContrMap : {A : 𝓤 ̇} {B : 𝓥 ̇} (f : A → B) → 𝓤 ⊔ 𝓥 ̇
isContrMap {B = B} f = (y : B) → isContr (fib f y)


-- Theorem 4.4.3 (contractible maps are haes).

isContrMap-to-ishae : {A : 𝓤 ̇} {B : 𝓥 ̇} (f : A → B) → isContrMap f → ishae f
isContrMap-to-ishae f P = g , pr₁ r , ε , pr₂ r
  where
  g = (λ y → pr₁ (pr₁ (P y)))
  ε = (λ y → pr₂ (pr₁ (P y)))
  r : rcoh f (g , ε)
  r = pr₁ (≃-sym (rcoh-≃-fib f (g , ε))) (λ x → pr₂ (P (f x)) (x , refl (f x)))


-- Theorem 4.4.4 (isContrMap is a proposition).

isContrMap-is-Prop : {A : 𝓤 ̇} {B : 𝓥 ̇} (f : A → B) → isProp (isContrMap f)
isContrMap-is-Prop f = Π-preserves-Props _ (λ y → isContr-is-Prop _)


-- Theorem 4.4.5 (isContrMap is equivalent to ishae).

isContrMap-≃-ishae : {A : 𝓤 ̇} {B : 𝓥 ̇} (f : A → B) → isContrMap f ≃ ishae f
isContrMap-≃-ishae f = biimplication-to-≃ _ _ (isContrMap-is-Prop _) (ishae-is-Prop _) (isContrMap-to-ishae _) (ishae-to-isContrMap _)

-- Corollary

isContrMap-≃-biinv : {A : 𝓤 ̇} {B : 𝓥 ̇} (f : A → B) → isContrMap f ≃ biinv f
isContrMap-≃-biinv f = (isContrMap-≃-ishae f) ● (≃-sym (biinv-≃-ishae f))

isContrMap-to-biinv : {A : 𝓤 ̇} {B : 𝓥 ̇} (f : A → B) → isContrMap f → biinv f
isContrMap-to-biinv f = pr₁ (isContrMap-≃-biinv f)

biinv-to-isContrMap : {A : 𝓤 ̇} {B : 𝓥 ̇} (f : A → B) → biinv f → isContrMap f
biinv-to-isContrMap f = pr₁ (≃-sym (isContrMap-≃-biinv f))


-- Corollary 4.4.6 (Can assume inhabited codomain).

module inhabited-codom-assum {A : 𝓤 ̇} {B : 𝓥 ̇} (f : A → B) where

  Contr : (B → isContrMap f) → isContrMap f
  Contr e y = e y y

  Hae : (B → ishae f) → ishae f
  Hae e = isContrMap-to-ishae f (Contr (λ y → ishae-to-isContrMap f (e y)))

  Biinv : (B → biinv f) → biinv f
  Biinv e = isContrMap-to-biinv f (Contr (λ y → biinv-to-isContrMap f (e y)))

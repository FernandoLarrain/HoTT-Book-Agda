{-# OPTIONS --without-K --exact-split #-}

open import Ch1.Type-theory
open import Ch2.Homotopy-type-theory
open import Ch3.Sets-and-logic
open import Ch4.3-Bi-invertible-maps
open import Ch4.6-Surjections-and-embeddings

module Ch7.2-UIP-and-Hedberg's-theorem where

-- Theorem 7.2.1 (Sets are precisely the types satisfying Axiom K).

_satisfies-Axiom-K : (X : 𝓤 ̇) → 𝓤 ̇
X satisfies-Axiom-K = (x : X) (p : x ≡ x) → p ≡ refl x 

isSet-iff-Axiom-K : (X : 𝓤 ̇) → (isSet X → X satisfies-Axiom-K) × (X satisfies-Axiom-K → isSet X)
isSet-iff-Axiom-K X = sufficiency , necessity where
  sufficiency : isSet X → X satisfies-Axiom-K
  sufficiency f x p = f x x p (refl x)
  necessity : (X satisfies-Axiom-K → isSet X)
  necessity k x .x p (refl .x) = k x p


-- -- Theorem 7.2.2 (A useful way to prove "sethood").

-- relation-implies-isSet : (X : 𝓤 ̇) (R : X → X → 𝓥 ̇) → ((x y : X) → isProp (R x y)) → ((x : X) → R x x) → ((x y : X) → R x y → x ≡ y) → isSet X × ((x y : X) → R x y ≃ (x ≡ y))
-- relation-implies-isSet X R mere-rel ρ f = {!first , second!} where
--   first : isSet X
--   first = {!!}
--   second : (x y : X) → R x y ≃ (x ≡ y)
--   second = {!!}

-- -- We need thm 4.4.7 first.

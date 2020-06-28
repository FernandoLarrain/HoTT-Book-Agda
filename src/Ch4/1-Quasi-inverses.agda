{-# OPTIONS --without-K --exact-split #-}

open import Ch1.Type-theory
open import Ch2.Homotopy-type-theory
open import Ch3.Sets-and-logic

module Ch4.1-Quasi-inverses where



-- Lemma 4.1.1

-- inhabited-qinv-is-id∼id : {A : 𝓤 ̇} {B : 𝓥 ̇} (f : A → B) → qinv f → qinv f ≃ ((x : A) → x ≡ x)  

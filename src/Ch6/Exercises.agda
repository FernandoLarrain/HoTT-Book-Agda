{-# OPTIONS --without-K --exact-split --rewriting #-}

open import Ch1.Type-theory
open import Ch2.Homotopy-type-theory
open import Ch3.Sets-and-logic
open import Ch6.2-Induction-pples-and-dependent-paths

module Ch6.Exercises where


-- -- Exercise 6.4 (n-spheres): Define dependent n-loops, the action of dependent functions on dependent n-loops and write down the induction principle for the n-spheres.


-- -- Characterization of loop spaces

-- -- Maybe define iterated Id and iterated refl and show that n-th loopspaces is an iterated Id over an iterated refl. Are the endpoints definitionally equal to an iterated refl?

-- -- Action on n-loops.

-- al : (n : ℕ) {A : 𝓤 ⊙} {B : 𝓥 ⊙} (f : A ⊙→ B) → pr₁ (Ω n A) → pr₁ (Ω  n B)
-- al zero (f , α) l = f l
-- al (succ n) {A , a} {B , b} (f , α) l = {!!}


-- -- The n-sphere.

-- postulate

--   -- (i) Type formation rule

--   Sphere : ℕ → 𝓤₀ ̇

--   -- (ii) Constructors

--   base : (n : ℕ) → Sphere n

--   loop- : (n : ℕ) → pr₁ (Ω n (Sphere n , base n))

-- module _ (n : ℕ) {B : 𝓤 ̇} (b : B) (l : pr₁ (Ω n (B , b))) where

--   -- (iii) Recursion principle

--   Sphere-rec : Sphere n → B
--   Sphere-rec = {!!}

--   -- (iv) Computation

--   base-β' : Sphere-rec (base n) ≡ b
--   base-β' = {!!} -- refl _

--   loop-β' : {!!}
--   loop-β' = {!!}

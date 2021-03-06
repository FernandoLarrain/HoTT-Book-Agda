{-# OPTIONS --without-K --exact-split #-}

open import Ch1.Type-theory
open import Ch2.Homotopy-type-theory
open import Ch3.Sets-and-logic
open import Ch4.Equivalences

module Ch5.1-Introduction-to-inductive-types where


-- Definition of the type of lists over a type A, List A.

data List {𝓤} (A : 𝓤 ̇) : 𝓤 ̇ where
  nil : List A
  _∷_ : A → List A → List A


-- Theorem 5.1.1 (Uniqueness principle for ℕ)

ℕ-uniqueness-pple' : (E : ℕ → 𝓤 ̇) (ez : E 0) (es : (n : ℕ) → E n → E (succ n)) (f g : Π E) → f 0 ≡ ez → ((n : ℕ) → f (succ n) ≡ es n (f n)) → g 0 ≡ ez → ((n : ℕ) → g (succ n) ≡ es n (g n)) → f ∼ g
ℕ-uniqueness-pple' E ez es f g fz fs gz gs = ℕ-induction _ (fz ∙ gz ⁻¹) λ n p → fs n ∙ ap (es n) p ∙ gs n ⁻¹


ℕ-uniqueness-pple : (E : ℕ → 𝓤 ̇) (ez : E 0) (es : (n : ℕ) → E n → E (succ n)) (f g : Π E) → f 0 ≡ ez → ((n : ℕ) → f (succ n) ≡ es n (f n)) → g 0 ≡ ez → ((n : ℕ) → g (succ n) ≡ es n (g n)) → f ≡ g
ℕ-uniqueness-pple E ez es f g fz fs gz gs = funext (ℕ-uniqueness-pple' E ez es f g fz fs gz gs)

{-# OPTIONS --without-K --exact-split #-}

open import Ch1.Type-theory
open import Ch2.Homotopy-type-theory
open import Ch3.Sets-and-logic

module Ch5.3-W-types where


-- Definition of W-types (well-founded trees).

data W {𝓤} {𝓥} (A : 𝓤 ̇) (B : A → 𝓥 ̇) : 𝓤 ⊔ 𝓥 ̇ where
  sup : (a : A) → (B a → W A B) → W A B

W-induction : {A : 𝓤 ̇} {B : A → 𝓥 ̇} (E : W A B → 𝓦 ̇) → ((a : A) (f : B a → W A B) → ((b : B a) → E (f b)) → E (sup a f)) → (w : W A B) → E w
W-induction E e (sup a f) = e a f λ b → W-induction E e (f b)

{- Should W-induction compute propositionally only? -}

W-recursion : {A : 𝓤 ̇} {B : A → 𝓥 ̇} (E : 𝓦 ̇) → ((a : A) → (B a → W A B) → (B a → E) → E) → W A B → E
W-recursion E e = W-induction (λ - → E) e


-- Examples of W-types.

ℕᵂ : 𝓤₀ ̇
ℕᵂ = W 𝟚 (𝟚-recursion _ 𝟘 𝟙)

Listᵂ : (A : 𝓤 ̇) → 𝓤 ̇
Listᵂ A = W (𝟙 + A) (+-recursion (λ u → 𝟘) λ a → 𝟙)


-- Theorem 5.3.1 (Uniqueness principle for W-types)

W-η : ⦃ fe : FunExt ⦄ {A : 𝓤 ̇} {B : A → 𝓥 ̇} (E : W A B → 𝓦 ̇) (e : (a : A) (f : B a → W A B) → ((b : B a) → E (f b)) → E (sup a f)) (g h : Π E) → ((a : A) (f : B a → W A B) → g (sup a f) ≡ e a f (g ∘ f)) → ((a : A) (f : B a → W A B) → h (sup a f) ≡ e a f (h ∘ f)) → g ≡ h
W-η E e g h βg βh = funext (W-induction _ (λ a f ih → βg a f ∙ ap (e a f) (funext ih) ∙ βh a f ⁻¹))

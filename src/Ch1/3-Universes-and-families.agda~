{-# OPTIONS --without-K --exact-split --safe #-}

module Ch1.3-Universes-and-families where


-- HoTT-Book notation for universes 

open import Agda.Primitive public
 renaming (
   Level to Universe ; -- We speak of universes rather than of levels
   lzero to 𝓤₀ ; -- Our first universe is called 𝓤₀
   lsuc to _⁺ ; -- The universe after 𝓤 is 𝓤 ⁺
   Setω to 𝓤ω -- There is a universe 𝓤ω strictly above 𝓤₀, 𝓤₁, ⋯ , 𝓤ₙ, ⋯
 )
 using (_⊔_) -- Least upper bound of two universes, e.g. 𝓤₀ ⊔ 𝓤₁ is 𝓤₁

Type = λ ℓ → Set ℓ

_̇   : (𝓤 : Universe) → Type (𝓤 ⁺) -- From universe as term to universe as type
𝓤 ̇  = Type 𝓤

𝓤₁ = 𝓤₀ ⁺
𝓤₂ = 𝓤₁ ⁺
𝓤₃ = 𝓤₂ ⁺

_⁺⁺ : Universe → Universe
𝓤 ⁺⁺ = 𝓤 ⁺ ⁺

universe-of : {𝓤 : Universe} (X : 𝓤 ̇ ) → Universe
universe-of {𝓤} X = 𝓤

type-of : {𝓤 : Universe} {X : 𝓤 ̇ } → X → 𝓤 ̇
type-of {𝓤} {X} x = X

infix  1 _̇


-- Cumulativity

variable
  𝓤 𝓥 𝓦 𝓣 : Universe

record Lift {𝓤 : Universe} (𝓥 : Universe) (X : 𝓤 ̇) : 𝓤 ⊔ 𝓥 ̇ where
  constructor
    lift
  field
    lower : X

open Lift public

Lift-induction : ∀ {𝓤} 𝓥 (X : 𝓤 ̇) (A : Lift 𝓥 X → 𝓦 ̇) → ((x : X) → A (lift x)) → (l : Lift 𝓥 X) → A l
Lift-induction 𝓥 X A φ (lift x) = φ x

Lift-recursion : ∀ {𝓤} 𝓥 {X : 𝓤 ̇ } {B : 𝓦 ̇ } → (X → B) → Lift 𝓥 X → B
Lift-recursion 𝓥 {X} {B} = Lift-induction 𝓥 X (λ _ → B)






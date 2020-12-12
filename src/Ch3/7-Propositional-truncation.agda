{-# OPTIONS --without-K --exact-split #-}

open import Ch1.Type-theory
open import Ch2.Homotopy-type-theory
open import Ch3.3-Mere-propositions

module Ch3.7-Propositional-truncation where


-- Definition of propositional truncations.

record PropTrunc : 𝓤ω where
  field
    ∥_∥₋₁ : {𝓤 : Universe} → 𝓤 ̇ → 𝓤 ̇ 
    ∣_∣₋₁ : {𝓤 : Universe} {X : 𝓤 ̇} → X → ∥ X ∥₋₁
    ∥∥₋₁-is-Prop : {𝓤 : Universe} {X : 𝓤 ̇} → isProp ∥ X ∥₋₁
    ∥∥₋₁-recursion : {𝓤 𝓥 : Universe} {X : 𝓤 ̇} {P : 𝓥 ̇} → isProp P → (X → P) → ∥ X ∥₋₁ → P
  infix 0 ∥_∥₋₁

open PropTrunc ⦃ ... ⦄ public

module _ ⦃ pt : PropTrunc ⦄ where


  -- Propositional computation rule for ∥∥-recursion

  ∣∣₋₁-prop-β' : {X : 𝓤 ̇} {P :  𝓥 ̇} → (i : isProp P) → (f : X → P) → (x : X) → ∥∥₋₁-recursion i f ∣ x ∣₋₁ ≡ f x
  ∣∣₋₁-prop-β' i f x = i (∥∥₋₁-recursion i f ∣ x ∣₋₁) (f x)


  -- ∥∥₋₁-induction

  ∥∥₋₁-induction : {X : 𝓤 ̇} {P : ∥ X ∥₋₁ → 𝓥 ̇} → ((s : ∥ X ∥₋₁) → isProp (P s)) → ((x : X) → P ∣ x ∣₋₁) → (s : ∥ X ∥₋₁) → P s
  ∥∥₋₁-induction {𝓤} {𝓥} {X} {P} i f s = φ' s
   where
    φ : X → P s
    φ x = transport P (∥∥₋₁-is-Prop ∣ x ∣₋₁ s) (f x)
    φ' : ∥ X ∥₋₁ → P s
    φ' = ∥∥₋₁-recursion (i s) φ


  -- Propositional computation rule for ∥∥-induction

  ∣∣₋₁-prop-β : {X : 𝓤 ̇} {P : ∥ X ∥₋₁ → 𝓥 ̇} → (i : (s : ∥ X ∥₋₁) → isProp (P s)) → (f : (x : X) → P ∣ x ∣₋₁) → (x : X) → ∥∥₋₁-induction i f ∣ x ∣₋₁ ≡ f x
  ∣∣₋₁-prop-β i f x = i ∣ x ∣₋₁ (∥∥₋₁-induction i f ∣ x ∣₋₁) (f x)


  -- Traditional logical connectives
  
  module disjunction where

    -- Definition

    _∨_ : 𝓤 ̇ → 𝓥 ̇ → 𝓤 ⊔ 𝓥 ̇
    A ∨ B = ∥ A + B ∥₋₁

    infixl 20 _∨_

    -- Closure

    ∨-is-Prop : {A : 𝓤 ̇} {B : 𝓥 ̇} → isProp (A ∨ B)
    ∨-is-Prop = ∥∥₋₁-is-Prop

    -- Disjunction elimination

    ∨-induction : {X : 𝓤 ̇} {Y : 𝓥 ̇} (A : X ∨ Y → 𝓦 ̇) → ((z : X ∨ Y) → isProp (A z)) → ((x : X) → A (∣ inl x ∣₋₁)) → ((y : Y) → A (∣ inr y ∣₋₁)) → (z : X ∨ Y) → A z
    ∨-induction A i f g = ∥∥₋₁-induction i (+-induction (A ∘ ∣_∣₋₁) f g)

    ∨-recursion : {X : 𝓤 ̇} {Y : 𝓥 ̇} {A : 𝓦 ̇} → isProp A → (X → A) → (Y → A) → X ∨ Y → A
    ∨-recursion {𝓤} {X} {Y} {A} i f g = ∥∥₋₁-recursion i (+-recursion f g)

  open disjunction public

  module existential where

    -- Definition

    ∃ : {X : 𝓤 ̇} → (X → 𝓥 ̇) → 𝓤 ⊔ 𝓥 ̇
    ∃ A = (∥ Σ A ∥₋₁)

    -∃ : {𝓤 𝓥 : Universe} (X : 𝓤 ̇) (Y : X → 𝓥 ̇) → 𝓤 ⊔ 𝓥 ̇
    -∃ X Y = ∃ Y

    syntax -∃ A (λ x → b) = ∃ x ꞉ A , b

    infixr -1 -∃

    -- Closure

    ∃-is-Prop : {X : 𝓤 ̇} {A : X → 𝓥 ̇} → isProp (∃ A)
    ∃-is-Prop = ∥∥₋₁-is-Prop

    -- Existential elimination

    ∃-induction : {X : 𝓤 ̇} {P : X → 𝓥 ̇} {Q : ∃ P → 𝓦 ̇} → ((z : ∃ P) → isProp (Q z)) → ((x : X) (u : P x) → Q ∣ (x , u) ∣₋₁) → (z : ∃ P) → Q z
    ∃-induction i g = ∥∥₋₁-induction i (Σ-induction g)

    ∃-recursion : {X : 𝓤 ̇} {P : X → 𝓥 ̇} {B : 𝓦 ̇} → isProp B → ((x : X) (u : P x) → B) → ∃ P → B
    ∃-recursion {𝓤} {X} {P} {B} i g = ∥∥₋₁-recursion i (Σ-induction g)

  open existential public

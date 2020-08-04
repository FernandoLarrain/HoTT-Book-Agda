{-# OPTIONS --without-K --exact-split --safe #-}

open import Ch1.Type-theory
open import Ch2.Homotopy-type-theory
open import Ch3.3-Mere-propositions

module Ch3.7-Propositional-truncation where


-- Definition of propositional truncations.

record PropTrunc : 𝓤ω where
  field
    ∥_∥ : {𝓤 : Universe} → 𝓤 ̇ → 𝓤 ̇ 
    ∣_∣ : {𝓤 : Universe} {X : 𝓤 ̇} → X → ∥ X ∥
    ∥∥-is-Prop : {𝓤 : Universe} {X : 𝓤 ̇} → isProp ∥ X ∥
    ∥∥-recursion : {𝓤 𝓥 : Universe} {X : 𝓤 ̇} {P : 𝓥 ̇} → isProp P → (X → P) → ∥ X ∥ → P
  infix 0 ∥_∥


open PropTrunc ⦃ ... ⦄

module _ ⦃ pt : PropTrunc ⦄ where

  -- Propositional computation rule for ∥∥-recursion

  ∣∣-prop-β' : {X : 𝓤 ̇} {P :  𝓥 ̇} → (i : isProp P) → (f : X → P) → (x : X) → ∥∥-recursion i f ∣ x ∣ ≡ f x
  ∣∣-prop-β' i f x = i (∥∥-recursion i f ∣ x ∣) (f x)


  -- ∥∥-induction

  ∥∥-induction : {X : 𝓤 ̇} {P : ∥ X ∥ → 𝓥 ̇} → ((s : ∥ X ∥) → isProp (P s)) → ((x : X) → P ∣ x ∣) → (s : ∥ X ∥) → P s
  ∥∥-induction {𝓤} {𝓥} {X} {P} i f s = φ' s
   where
    φ : X → P s
    φ x = transport P (∥∥-is-Prop ∣ x ∣ s) (f x)
    φ' : ∥ X ∥ → P s
    φ' = ∥∥-recursion (i s) φ


  -- Propositional computation rule for ∥∥-induction

  ∣∣-prop-β : {X : 𝓤 ̇} {P : ∥ X ∥ → 𝓥 ̇} → (i : (s : ∥ X ∥) → isProp (P s)) → (f : (x : X) → P ∣ x ∣) → (x : X) → ∥∥-induction i f ∣ x ∣ ≡ f x
  ∣∣-prop-β i f x = i ∣ x ∣ (∥∥-induction i f ∣ x ∣) (f x)


  -- Traditional logical connectives
  
  module disjunction where

    -- Definition

    _∨_ : 𝓤 ̇ → 𝓥 ̇ → 𝓤 ⊔ 𝓥 ̇
    A ∨ B = ∥ A + B ∥

    infixl 20 _∨_

    -- Closure

    ∨-is-Prop : {A : 𝓤 ̇} {B : 𝓥 ̇} → isProp (A ∨ B)
    ∨-is-Prop = ∥∥-is-Prop

    -- Disjunction elimination

    ∨-induction : {X : 𝓤 ̇} {Y : 𝓥 ̇} (A : X ∨ Y → 𝓦 ̇) → ((z : X ∨ Y) → isProp (A z)) → ((x : X) → A (∣ inl x ∣)) → ((y : Y) → A (∣ inr y ∣)) → (z : X ∨ Y) → A z
    ∨-induction A i f g = ∥∥-induction i (+-induction (A ∘ ∣_∣) f g)

    ∨-recursion : {X : 𝓤 ̇} {Y : 𝓥 ̇} {A : 𝓦 ̇} → isProp A → (X → A) → (Y → A) → X ∨ Y → A
    ∨-recursion {X = X} {Y} {A} i f g = ∥∥-recursion i (+-recursion f g)

  open disjunction public

  module existential where

    -- Definition

    ∃ : {X : 𝓤 ̇} → (X → 𝓥 ̇) → 𝓤 ⊔ 𝓥 ̇
    ∃ A = (∥ Σ A ∥)

    -∃ : {𝓤 𝓥 : Universe} (X : 𝓤 ̇) (Y : X → 𝓥 ̇) → 𝓤 ⊔ 𝓥 ̇
    -∃ X Y = ∃ Y

    syntax -∃ A (λ x → b) = ∃ x ꞉ A , b

    infixr -1 -∃

    -- Closure

    ∃-is-Prop : {X : 𝓤 ̇} {A : X → 𝓥 ̇} → isProp (∃ A)
    ∃-is-Prop = ∥∥-is-Prop

    -- Existential elimination

    ∃-induction : {X : 𝓤 ̇} {P : X → 𝓥 ̇} {Q : ∃ P → 𝓦 ̇} → ((z : ∃ P) → isProp (Q z)) → ((x : X) (u : P x) → Q ∣ (x , u) ∣) → (z : ∃ P) → Q z
    ∃-induction i g = ∥∥-induction i (Σ-induction g)

    ∃-recursion : {X : 𝓤 ̇} {P : X → 𝓥 ̇} {B : 𝓦 ̇} → isProp B → ((x : X) (u : P x) → B) → ∃ P → B
    ∃-recursion {B = B} i g = ∥∥-recursion i (Σ-induction g)

  open existential public

{-# OPTIONS --without-K --exact-split --safe #-}

open import Ch1.Type-theory
open import Ch2.Homotopy-type-theory
open import Ch3.Sets-and-logic
open import Ch4.Equivalences
open import Ch6.9-Truncations
open import Ch7.1-Definition-of-n-types
open import Ch7.3-Truncations-safe

module Ch7.5-Connectedness ⦃ tc : Truncations ⦄ where


-- Definition 7.5.1 (n-connected types and functions).

is_connected_ : Tlevel → 𝓤 ̇ → 𝓤 ̇
is n connected A = isContr (∥ A ∥ n)

conn : Tlevel → {A : 𝓤 ̇} {B : 𝓥 ̇} → (A → B) → 𝓤 ⊔ 𝓥 ̇
conn n {A} {B} f = (b : B) → isContr (∥ fib f b ∥ n)

conn-is-Prop : ⦃ fe : FunExt ⦄ (n : Tlevel) {A : 𝓤 ̇} {B : 𝓥 ̇} (f : A → B) → isProp (conn n f)
conn-is-Prop n f = Π-preserves-Props _ λ b → isContr-is-Prop _


-- Lemma 7.5.2. (f is -1-connected iff it is surjective).

conn-⟨-1⟩-≃-isSurjective : ⦃ fe : FunExt ⦄ {A : 𝓤 ̇} {B : 𝓥 ̇} (f : A → B) → conn ⟨-1⟩ f ≃ isSurjective f
conn-⟨-1⟩-≃-isSurjective f = Π-preserves-family-≃ (λ b → ⇔-to-≃ (isContr-is-Prop _) ∃-is-Prop (isProp-to-isContr-iff-is-inhabited ∃-is-Prop))


-- Definition (Connected , simply connected).

is-connected : 𝓤 ̇ → 𝓤 ̇
is-connected A = is ⟨0⟩ connected A

is-simply-connected : 𝓤 ̇ → 𝓤 ̇
is-simply-connected A = is ⟨1⟩ connected A


-- Lemma 7.5.4 (Retractions of maps preserve connectedness).

retractions-of-maps-preserve-conn : (n : Tlevel) {A : 𝓤 ̇} {B : 𝓥 ̇} {X : 𝓦 ̇} {Y : 𝓣 ̇} {g : A → B} {f : X → Y} → g is-retract-of f → conn n f → conn n g
retractions-of-maps-preserve-conn n ρ i b = retract-of-Contr-is-Contr (∥∥-preserves-◁ (retraction-of-maps-to-fiberwise-retraction ρ b)) (i _)


-- Corollary 7.5.5 (Homotopy preserves connectedness).

∼-preserves-conn : (n : Tlevel) {A : 𝓤 ̇} {B : 𝓥 ̇} {f g : A → B} → f ∼ g → conn n f → conn n g
∼-preserves-conn n = retractions-of-maps-preserve-conn n ∘ ∼-to-retract


-- Lemma 7.5.6.

conn-∘ : (n : Tlevel) {A : 𝓤 ̇} {B : 𝓥 ̇} {C : 𝓦 ̇} {f : A → B} {g : B → C} → conn n f → conn n g ⇔ conn n (g ∘ f)
conn-∘ n {A} {B} {C} {f} {g} f-is-conn = (λ f-is-conn c → ≃-preserves-Contr (≃-sym (aux-≃ c)) (f-is-conn c)) , λ ∘-is-conn c → ≃-preserves-Contr (aux-≃ c) (∘-is-conn c) where
  aux-≃ : (c : C) → (∥ fib (g ∘ f) c ∥ n) ≃ (∥ fib g c ∥ n)
  aux-≃ c =
    (∥ fib (g ∘ f) c ∥ n)
      ≃⟨ ∥∥-preserves-≃ (fib-∘ f g c) ⟩
    ∥ Σ w ꞉ fib g c , fib f (pr₁ w) ∥ n
      ≃⟨ ≃-sym ∥∥-preserves-Σ.equiv ⟩
    ∥ Σ w ꞉ fib g c , ∥ fib f (pr₁ w) ∥ n ∥ n
      ≃⟨ ∥∥-preserves-≃ (Σ-of-Contr-family-is-base _ _ (f-is-conn ∘ pr₁)) ⟩
    (∥ fib g c ∥ n) ■


-- Lemma 7.5.7.

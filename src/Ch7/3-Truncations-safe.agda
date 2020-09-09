{-# OPTIONS --without-K --exact-split --safe #-}

open import Ch1.Type-theory
open import Ch2.Homotopy-type-theory
open import Ch3.Sets-and-logic
open import Ch4.Equivalences
open import Ch6.9-Truncations
open import Ch7.1-Definition-of-n-types

module Ch7.3-Truncations-safe where


record Truncations : 𝓤ω where
  field
    Truncation : {𝓤 : Universe} → Tlevel → 𝓤 ̇ → 𝓤 ̇
    ∣_∣ : {𝓤 : Universe} {n : Tlevel} {A : 𝓤 ̇} → A → Truncation n A
    ∥∥-Tlevel : {𝓤 : Universe} {n : Tlevel} {A : 𝓤 ̇} → is n type (Truncation n A)
    ∥∥-induction : {𝓤 𝓥 : Universe} {n : Tlevel} {A : 𝓤 ̇} {P : Truncation n A → 𝓥 ̇} → ((x : Truncation n A) → is n type (P x)) → Π (P ∘ ∣_∣) → Π P
    ∣∣-prop-β : {𝓤 𝓥 : Universe} {n : Tlevel} {A : 𝓤 ̇} {P : Truncation n A → 𝓥 ̇} (i : (x : Truncation n A) → is n type (P x)) (g : Π (P ∘ ∣_∣)) → ∥∥-induction i g ∘ ∣_∣ ∼ g

  syntax Truncation n A = ∥ A ∥ n

open Truncations ⦃ ... ⦄ public

module _ ⦃ tc : Truncations ⦄ where

  -- Recursion principle of n-truncation

  ∥∥-recursion : {n : Tlevel} {A : 𝓤 ̇} {B : 𝓥 ̇} → is n type B → (A → B) → ∥ A ∥ n → B
  ∥∥-recursion i g = ∥∥-induction (λ - → i) g

  -- Propositional computation rule for ∥∥-recursion

  ∣∣-prop-β' : {n : Tlevel} {A : 𝓤 ̇} {B : 𝓥 ̇} (i : is n type B) (g : A → B) → ∥∥-recursion i g ∘ ∣_∣ ∼ g
  ∣∣-prop-β' i g = ∣∣-prop-β (λ - → i) g

  -- Uniqueness principle of n-truncation

  ∥∥-uniqueness-pple : {n : Tlevel} {A : 𝓤 ̇} {B : 𝓥 ̇} → is n type B → {f f' : ∥ A ∥ n → B} → f ∘ ∣_∣ ∼ f' ∘ ∣_∣ → f ∼ f'
  ∥∥-uniqueness-pple {𝓤} {𝓥} {n} {A} {B} i {f} {f'} agreement = ∥∥-induction (λ x → Tlevel-is-cumulative i _ _) agreement

  -- UMP of n-truncations

  module ∥∥-UMP ⦃ fe : FunExt ⦄ (n : Tlevel) (A : 𝓤 ̇) {B : 𝓥 ̇} (i : is n type B) where

    ϕ : (∥ A ∥ n → B) → (A → B)
    ϕ f = f ∘ ∣_∣

    ψ : (A → B) → ∥ A ∥ n → B
    ψ = ∥∥-recursion i

    β : ϕ ∘ ψ ∼ id
    β g = funext (∣∣-prop-β' i g)

    η : ψ ∘ ϕ ∼ id
    η f = funext (∥∥-uniqueness-pple i (∣∣-prop-β' i (ϕ f)))

    equiv : (∥ A ∥ n → B) ≃ (A → B)
    equiv = ϕ , (qinv-to-isequiv (ψ , β , η))

  -- Relation to old definitions

  instance
    pt : PropTrunc
    PropTrunc.∥ pt ∥₋₁ = Truncation ⟨-1⟩
    PropTrunc.∣ pt ∣₋₁ = ∣_∣
    PropTrunc.∥∥₋₁-is-Prop pt = pr₂ Prop-iff-Contr-≡ ∥∥-Tlevel
    PropTrunc.∥∥₋₁-recursion pt = ∥∥-recursion ∘ pr₁ Prop-iff-Contr-≡

  instance
    st : SetTrunc
    SetTrunc.∥ st ∥₀ = Truncation ⟨0⟩
    SetTrunc.∣ st ∣₀ = ∣_∣
    SetTrunc.∥∥₀-is-Set st = pr₂ isSet-iff-is-⟨0⟩-type ∥∥-Tlevel
    SetTrunc.∥∥₀-induction st = ∥∥-induction ∘ λ i x → pr₁ isSet-iff-is-⟨0⟩-type (i x)
    SetTrunc.∣∣₀-prop-β st = ∣∣-prop-β ∘ λ i x → pr₁ isSet-iff-is-⟨0⟩-type (i x)
 

  -- Truncation is functorial

  ∥∥-map : (n : Tlevel) {A : 𝓤 ̇} {B : 𝓥 ̇} → (A → B) → ∥ A ∥ n → ∥ B ∥ n
  ∥∥-map n {A} {B} f = ∥∥-recursion ∥∥-Tlevel (∣_∣ ∘ f)

  ∥∥-map-β : (n : Tlevel) {A : 𝓤 ̇} {B : 𝓥 ̇} (f : A → B) → ∥∥-map n f ∘ ∣_∣ ∼ ∣_∣ ∘ f
  ∥∥-map-β n f = ∣∣-prop-β' ∥∥-Tlevel (∣_∣ ∘ f) 

  ∥∥-∘ : {n : Tlevel} {A : 𝓤 ̇} {B : 𝓥 ̇} {C : 𝓦 ̇} (f : A → B) (g : B → C) → ∥∥-map n (g ∘ f) ∼ ∥∥-map n g ∘ ∥∥-map n f
  ∥∥-∘ {𝓤} {𝓥} {𝓦} {n} f g = ∥∥-uniqueness-pple ∥∥-Tlevel (λ a → ∥∥-map-β n (g ∘ f) a ∙ ∥∥-map-β n g (f a) ⁻¹ ∙ ap (∥∥-map n g)  (∥∥-map-β n f a ⁻¹))

  ∥∥-𝑖𝑑 : {n : Tlevel} (A : 𝓤 ̇) → ∥∥-map n (𝑖𝑑 A) ∼ 𝑖𝑑 (∥ A ∥ n)
  ∥∥-𝑖𝑑 {𝓤} {n} A = ∥∥-uniqueness-pple ∥∥-Tlevel (∣∣-prop-β' ∥∥-Tlevel (∣_∣ ∘ 𝑖𝑑 A))


  -- ∣_∣ is natural

  ∣∣-nat : (n : Tlevel) {A : 𝓤 ̇} {B : 𝓥 ̇} (f : A → B) → ∥∥-map n f ∘  ∣_∣ ∼ ∣_∣ ∘ f
  ∣∣-nat n f = ∣∣-prop-β' ∥∥-Tlevel (∣_∣ ∘ f)


  -- Lemma 7.3.5 (Higher functoriality of Truncation)

  ∥∥-∼ : (n : Tlevel) {A : 𝓤 ̇} {B : 𝓥 ̇} {f g : A → B} → f ∼ g → ∥∥-map n f ∼ ∥∥-map n g
  ∥∥-∼ n {A} {B} {f} {g} α = ∥∥-uniqueness-pple ∥∥-Tlevel (λ a → ∣∣-nat n f a ∙ ap ∣_∣ (α a) ∙ (∣∣-nat n g a) ⁻¹)
  
  ∥∥-∼-is-ap-∣∣ : (n : Tlevel) {A : 𝓤 ̇} {B : 𝓥 ̇} {f g : A → B} (α : f ∼ g) (a : A) → ∣∣-nat n f a ⁻¹ ∙ ∥∥-∼ n α ∣ a ∣ ∙ ∣∣-nat n g a ≡ ap ∣_∣ (α a)
  ∥∥-∼-is-ap-∣∣ n {A} {B} {f} {g} α a = ap (λ - → ∣∣-nat n f a ⁻¹ ∙ - ∙ ∣∣-nat n g a) (∣∣-prop-β _ _ _) ∙ ((∙-assoc _ _ _ ∙ ((∙-assoc _ _ _ ∙ ((linv _ ∙ᵣ ap ∣_∣ (α a)) ∙ lu _ ⁻¹)) ∙ᵣ ∣∣-nat n g a ⁻¹)) ∙ᵣ ∣∣-nat n g a) ∙ (∙-assoc _ _ _ ⁻¹ ∙ (ap ∣_∣ (α a) ∙ₗ linv _) ∙ ru _ ⁻¹)


  -- Corollary: Truncation preserves retractions.

  ∥∥-preserves-◁ : {n : Tlevel} {A : 𝓤 ̇} {B : 𝓥 ̇} → B ◁ A → (∥ B ∥ n) ◁ (∥ A ∥ n)
  ∥∥-preserves-◁ {𝓤} {𝓥} {n} {A} {B} (r , s , α) = ∥∥-map n r , ∥∥-map n s , (hsym (∥∥-∘ s r) · ∥∥-∼ n α · ∥∥-𝑖𝑑 B)


  -- Corollary : Truncation preserves quasi-inverses.

  ∥∥-preserves-qinv : {n : Tlevel} {A : 𝓤 ̇} {B : 𝓥 ̇} (f : A → B) → qinv f → qinv (∥∥-map n f)
  ∥∥-preserves-qinv {𝓤} {𝓥} {n} {A} {B} f (g , α , β) = ∥∥-map n g , (hsym (∥∥-∘ g f) · ∥∥-∼ n α ·  ∥∥-𝑖𝑑 B) , (hsym (∥∥-∘ f g) · ∥∥-∼ n β · ∥∥-𝑖𝑑 A )


  -- Corollary : Truncation preserves equivalences.

  ∥∥-preserves-≃ : {n : Tlevel} {A : 𝓤 ̇} {B : 𝓥 ̇} → A ≃ B → (∥ A ∥ n ) ≃ (∥ B ∥ n)
  ∥∥-preserves-≃ {𝓤} {𝓥} {n} {A} {B} (f , e) = ∥∥-map n f , qinv-to-isequiv (∥∥-preserves-qinv f (isequiv-to-qinv e))


  -- Corollary 7.3.7 (A is n-type iff ∣_∣ : A → ∥ A ∥ n is an equivalence).

  has-Tlevel-≃-∣∣-is-equiv : ⦃ fe : FunExt ⦄ (n : Tlevel) (A : 𝓤 ̇) → is n type A ≃ isequiv (∣_∣ {𝓤} {n} {A})
  has-Tlevel-≃-∣∣-is-equiv {𝓤} n A = ⇔-to-≃ (Tlevel-is-predicate _ _) (ishae-is-Prop _) (
    (λ i → qinv-to-isequiv (∥∥-recursion i id , ∥∥-uniqueness-pple ∥∥-Tlevel (λ x → ap ∣_∣ (∣∣-prop-β' i id x)) , ∣∣-prop-β' _ _)) ,
    (λ i → ≃-preserves-Tlevel n _ _ (≃-sym (∣_∣ , i)) ∥∥-Tlevel)
    )


  -- Theorem 7.3.8 (Truncation preserves finite products).

  module ∥∥-preserves-× ⦃ fe : FunExt ⦄ {n : Tlevel} {A : 𝓤 ̇} {B : 𝓥 ̇} where

    -- (i) UMP of product of truncations

    ×-∥∥-UMP : {C : 𝓦 ̇} → is n type C → ((∥ A ∥ n) × (∥ B ∥ n) → C) ≃ ((A × B) → C)
    ×-∥∥-UMP {𝓦} {C} i =
      ((∥ A ∥ n) × (∥ B ∥ n) → C)
        ≃⟨ GCCAdj (∥ A ∥ n) (λ - → ∥ B ∥ n) (λ - → C) ⟩
      (∥ A ∥ n → ∥ B ∥ n → C)
        ≃⟨ →-preserves-codom-≃ _ (∥∥-UMP.equiv n B i) ⟩
      (∥ A ∥ n → B → C)
        ≃⟨ ∥∥-UMP.equiv n A (→-preserves-Tlevel n B C i) ⟩
      (A → B → C)
        ≃⟨ ≃-sym (GCCAdj A (λ - → B) (λ - → C)) ⟩
      (A × B → C) ■

    _ : {C : 𝓦 ̇} (i : is n type C) → pr₁ (×-∥∥-UMP i) ∼ _∘ ×-map ∣_∣ ∣_∣
    _ = λ i → hrefl _

    ×-∥∥-recursion : {C : 𝓦 ̇} → is n type C → (A × B → C) → (∥ A ∥ n) × (∥ B ∥ n) → C
    ×-∥∥-recursion i = inv (×-∥∥-UMP i)

    ×-∥∥-β : {C : 𝓦 ̇} (i : is n type C) → (_∘ ×-map ∣_∣ ∣_∣) ∘ ×-∥∥-recursion i ∼ id
    ×-∥∥-β i = isequiv₃ (pr₂ (×-∥∥-UMP i))

    ×-∥∥-η : {C : 𝓦 ̇} (i : is n type C) → ×-∥∥-recursion i ∘ (_∘ ×-map ∣_∣ ∣_∣) ∼ id
    ×-∥∥-η i = isequiv₂ (pr₂ (×-∥∥-UMP i))

    -- (ii) UMP gives equivalence

    ϕ : ∥ A × B ∥ n → (∥ A ∥ n) × (∥ B ∥ n)
    ϕ = ∥∥-recursion (×-preserves-Tlevel n _ _ ∥∥-Tlevel ∥∥-Tlevel) (×-map ∣_∣ ∣_∣)

    ϕ-comm : ϕ ∘ ∣_∣ ≡ ×-map ∣_∣ ∣_∣
    ϕ-comm = funext (∣∣-prop-β' (×-preserves-Tlevel n _ _ ∥∥-Tlevel ∥∥-Tlevel) (×-map ∣_∣ ∣_∣))

    ψ : (∥ A ∥ n) × (∥ B ∥ n) → ∥ A × B ∥ n
    ψ = ×-∥∥-recursion ∥∥-Tlevel ∣_∣

    ψ-comm : ψ ∘ ×-map ∣_∣ ∣_∣ ≡ ∣_∣
    ψ-comm = ×-∥∥-β ∥∥-Tlevel ∣_∣

    α : ϕ ∘ ψ ∼ 𝑖𝑑 ((∥ A ∥ n) × (∥ B ∥ n))
    α = let i : is n type ((∥ A ∥ n) × (∥ B ∥ n))
            i = ×-preserves-Tlevel n _ _ ∥∥-Tlevel ∥∥-Tlevel
        in happly (
           ϕ ∘ ψ
             ≡⟨ ×-∥∥-η i (ϕ ∘ ψ) ⁻¹ ⟩
           ×-∥∥-recursion i (ϕ ∘ ψ ∘ ×-map ∣_∣ ∣_∣)
             ≡⟨ ap (×-∥∥-recursion i) (ap (ϕ ∘_) ψ-comm ∙ ϕ-comm ) ⟩
           ×-∥∥-recursion i (id ∘ ×-map ∣_∣ ∣_∣)
             ≡⟨ ×-∥∥-η i id ⟩
           id ∎
           )

    β : ψ ∘ ϕ ∼ 𝑖𝑑 (∥ A × B ∥ n)
    β = ∥∥-uniqueness-pple ∥∥-Tlevel (happly (ap (ψ ∘_) ϕ-comm ∙ ψ-comm))

    equiv : (∥ A × B ∥ n) ≃ (∥ A ∥ n) × (∥ B ∥ n)
    equiv = ϕ , qinv-to-isequiv (ψ , α , β)


  -- Theorem 7.3.9 (Truncation preserves Σ).

  module ∥∥-preserves-Σ {n : Tlevel} {A : 𝓤 ̇} {P : A → 𝓥 ̇} where

    ϕ : ∥ Σ x ꞉ A , ∥ P x ∥ n ∥ n → ∥ Σ P ∥ n
    ϕ = ∥∥-recursion ∥∥-Tlevel (Σ-induction (λ a → ∥∥-recursion ∥∥-Tlevel (λ u → ∣ (a , u) ∣)))

    ψ : ∥ Σ P ∥ n → ∥ Σ x ꞉ A , ∥ P x ∥ n ∥ n
    ψ = ∥∥-recursion ∥∥-Tlevel (Σ-induction λ a u → ∣ (a , ∣ u ∣) ∣)

    H : ϕ ∘ ψ ∼ id
    H = ∥∥-uniqueness-pple ∥∥-Tlevel (Σ-induction λ a u → ap ϕ (∣∣-prop-β' ∥∥-Tlevel _ _) ∙ (∣∣-prop-β' ∥∥-Tlevel _ _) ∙ ∣∣-prop-β' ∥∥-Tlevel _ _)

    K : ψ ∘ ϕ ∼ id
    K = ∥∥-uniqueness-pple ∥∥-Tlevel (Σ-induction (λ a → ∥∥-uniqueness-pple ∥∥-Tlevel (λ u → ap ψ (∣∣-prop-β' ∥∥-Tlevel _ _ ∙ ∣∣-prop-β (λ u → ∥∥-Tlevel) _ _) ∙ ∣∣-prop-β' ∥∥-Tlevel _ _)))

    equiv : (∥ Σ x ꞉ A , ∥ P x ∥ n ∥ n) ≃ (∥ Σ P ∥ n)
    equiv = ϕ , qinv-to-isequiv (ψ , H , K)


  -- Corollary 7.3.10 (Sum of truncated family over n-type is n-truncation of sum).

  ∥∥-preserves-Σ : ⦃ fe : FunExt ⦄ {n : Tlevel} {A : 𝓤 ̇} {P : A → 𝓥 ̇} → is n type A → (Σ x ꞉ A , ∥ P x ∥ n) ≃ (∥ Σ P ∥ n)
  ∥∥-preserves-Σ {𝓤} {𝓥} {n} {A} {P} i = ∣_∣ , (pr₁ (has-Tlevel-≃-∣∣-is-equiv n (Σ x ꞉ A , ∥ P x ∥ n)) (Σ-preserves-Tlevel n _ (λ a → ∥ P a ∥ n) i (λ - → ∥∥-Tlevel))) ● ∥∥-preserves-Σ.equiv
  
  
  -- Lemma 7.3.15 (Cumulativity of truncations).

  ∥∥-is-cumulative : ⦃ fe : FunExt ⦄ (n : Tlevel) (A : 𝓤 ̇) (k : ℕ) → (∥ ∥ A ∥ (S^ k n) ∥ n) ≃ (∥ A ∥ n)
  ∥∥-is-cumulative n A k = f , qinv-to-isequiv (g , α , β) where
    t : is (S^ k n) type (∥ A ∥ n)
    t = Tlevel-is-cumulative' k ∥∥-Tlevel
    t' : is (S^ k n) type (∥ ∥ A ∥ (S^ k n) ∥ n)
    t' = Tlevel-is-cumulative' k ∥∥-Tlevel
    f : ∥ ∥ A ∥ (S^ k n) ∥ n → ∥ A ∥ n
    f = ∥∥-recursion ∥∥-Tlevel (∥∥-recursion t ∣_∣)
    g : ∥ A ∥ n → (∥ ∥ A ∥ (S^ k n) ∥ n)
    g = ∥∥-recursion ∥∥-Tlevel (∣_∣ ∘ ∣_∣)
    α : f ∘ g ∼ id
    α = ∥∥-uniqueness-pple ∥∥-Tlevel (λ a → ap f (∣∣-prop-β' ∥∥-Tlevel (∣_∣ ∘ ∣_∣) a) ∙ (∣∣-prop-β' ∥∥-Tlevel (∥∥-recursion t ∣_∣) ∣ a ∣ ∙ ∣∣-prop-β' t ∣_∣ a ))
    β : g ∘ f ∼ id
    β = ∥∥-uniqueness-pple ∥∥-Tlevel ((λ x → ap g (∣∣-prop-β' ∥∥-Tlevel (∥∥-recursion t ∣_∣) x)) · ∥∥-uniqueness-pple t' λ a → ap g (∣∣-prop-β' t ∣_∣ a) ∙ ∣∣-prop-β' ∥∥-Tlevel (∣_∣ ∘ ∣_∣) a)
  



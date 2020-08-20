{-# OPTIONS --without-K --exact-split --rewriting #-}

open import Ch1.Type-theory
open import Ch2.Homotopy-type-theory
open import Ch3.Sets-and-logic
open import Ch4.Equivalences
open import Rewrite
open import Ch6.2-Induction-pples-and-dependent-paths
open import Ch6.5-Suspensions
open import Ch7.1-Definition-of-n-types
open import Ch7.2-UIP-and-Hedberg's-theorem

module Ch7.3-Truncations ⦃ fe : FunExt ⦄ ⦃ univ : Univalence ⦄ where

-- Definition of n-truncation of a type. 

postulate

  -- (i) Type formation rule

  Trunc : Tlevel → 𝓤 ̇ → 𝓤 ̇

  -- (ii) Constructors
  
  -- General point constructor:

  [_] : {n : Tlevel} {A : 𝓤 ̇} → A → Trunc n A

  -- Hub constructor:

hub-codom : Tlevel → 𝓤 ̇ → 𝓤 ̇
hub-codom ⟨-2⟩ A = Trunc ⟨-2⟩ A
hub-codom (S n) A = (Sphere (to-ℕ n) → Trunc (S n) A) → Trunc (S n) A

postulate

  hub : {n : Tlevel} {A : 𝓤 ̇} → hub-codom n A

  -- Spoke constructor:

spoke-codom : Tlevel → 𝓤 ̇ → 𝓤 ̇
spoke-codom ⟨-2⟩ A = (x : Trunc ⟨-2⟩ A) → hub ≡ x
spoke-codom (S n) A = (r : Sphere (to-ℕ n) → Trunc (S n) A) (x : Sphere (to-ℕ n)) → r x ≡ hub r

postulate

  spoke : (n : Tlevel) {A : 𝓤 ̇} → spoke-codom n A

  -- (iii) Induction principle

Trunc-ind-data : (n : Tlevel) (A : 𝓤 ̇) (P : Trunc n A → 𝓥 ̇) → Π (P ∘ [_]) → 𝓤 ⊔ 𝓥 ̇

Trunc-ind-data ⟨-2⟩ A P g =
  Σ h ꞉ P hub ,
  ((x : Trunc ⟨-2⟩ A) (u : P x) → h ≡ u [ P ↓ spoke ⟨-2⟩ x ])

Trunc-ind-data (S n) A P g =
  Σ h ꞉ ((r : Sphere (to-ℕ n) → Trunc (S n) A) → ((x : Sphere (to-ℕ n)) → P (r x)) → P (hub r)) ,
  ((r : Sphere (to-ℕ n) → Trunc (S n) A) (r' : (x : Sphere (to-ℕ n)) → P (r x)) (x : Sphere (to-ℕ n)) → r' x ≡ h r r' [ P ↓ spoke (S n) r x ])

postulate

  Trunc-ind : {n : Tlevel} {A : 𝓤 ̇} {P : Trunc n A → 𝓥 ̇} (g : Π (P ∘ [_])) → Trunc-ind-data n A P g → Π P

  -- (iv) Computation rule for Trunc-ind ⟨-2⟩

  []-β : (n : Tlevel) (A : 𝓤 ̇) (P : Trunc n A → 𝓥 ̇) (g : Π (P ∘ [_])) (d : Trunc-ind-data n A P g) (a : A) →  Trunc-ind g d [ a ] ↦ g a

  {-# REWRITE []-β #-}

_ : (n : Tlevel) (A : 𝓤 ̇) (P : Trunc n A → 𝓥 ̇) (g : Π (P ∘ [_])) (d : Trunc-ind-data n A P g) →  Trunc-ind g d ∘ [_] ∼ g
_ = λ n A P g d x → refl _


-- Lemma 7.3.1 (n-truncations are n-types).

Trunc-Tlevel : {n : Tlevel} {A : 𝓤 ̇} → is n type (Trunc n A)
Trunc-Tlevel {𝓤} {⟨-2⟩} {A} = hub , spoke ⟨-2⟩
Trunc-Tlevel {𝓤} {(S n)} {A} = pr₁ (≃-sym (Tlevel-in-terms-of-Map⊙ n (Trunc (S n) A))) (λ b → ((λ x → b) , (refl b)) , (Σ-induction λ r p → (dpair-≡ (q r b p , (transport-funval-≡' (base (to-ℕ n)) b (q r b p) p ∙ (ap (λ - → - ⁻¹ ∙ p) (happly-β (λ x → spoke (S n) r x ∙ spoke (S n) r (base (to-ℕ n)) ⁻¹ ∙ p) (base (to-ℕ n)) ∙ (rinv _ ∙ᵣ p) ∙ lu _ ⁻¹) ∙ linv p)))) ⁻¹)) where
  q : (r : Sphere (to-ℕ n) → Trunc (S n) A) (b : Trunc (S n) A) (p : r (base (to-ℕ n)) ≡ b) → r ≡ λ x → b
  q r b p = funext λ x → spoke (S n) r x ∙ spoke (S n) r (base (to-ℕ n)) ⁻¹ ∙ p


-- Theorem 7.3.2 (Better induction principle for truncations)

Trunc-ind' : {n : Tlevel} {A : 𝓤 ̇} {P : Trunc n A → 𝓥 ̇} → ((x : Trunc n A) → is n type (P x)) → Π (P ∘ [_]) → Π P
Trunc-ind' {𝓤} {𝓥} {⟨-2⟩} {A} {P} i g = Trunc-ind {𝓤} {𝓥} {⟨-2⟩} {A} {P} g (
  (pr₁ (i hub)) ,
  (λ x u → pr₂ (pr₁ isContr-iff-is-inhabited-Prop (i x)) _ _)
  )
Trunc-ind' {𝓤} {𝓥} {S n} {A} {P} i g = Trunc-ind {𝓤} {𝓥} {S n} {A} {P} g (u , v)
  where
  t : (r : Sphere (to-ℕ n) → Trunc (S n) A) (r' : (x : Sphere (to-ℕ n)) → P (r x)) → Sphere (to-ℕ n) → P (hub r)
  t r r' = λ x → transport P (spoke (S n) r x) (r' x)
  u : (r : Sphere (to-ℕ n) → Trunc (S n) A) (r' : (x : Sphere (to-ℕ n)) → P (r x)) → P (hub r)
  u r r' = pr₁ (hub-and-spokes n (P (hub r)) (i (hub r)) (t r r'))
  v : (r : Sphere (to-ℕ n) → Trunc (S n) A) (r' : (x : Sphere (to-ℕ n)) → P (r x)) (x : Sphere (to-ℕ n)) → t r r' x ≡ u r r'
  v r r' = pr₂ (hub-and-spokes n (P (hub r)) (i (hub r)) (t r r'))
  
-- Computation rule: we only get definitional equality after pattern-matching on n.

Trunc-ind'-β : {n : Tlevel} {A : 𝓤 ̇} {P : Trunc n A → 𝓥 ̇} (i : (x : Trunc n A) → is n type (P x)) (g : Π (P ∘ [_])) → Trunc-ind' i g ∘ [_] ∼ g
Trunc-ind'-β {𝓤} {𝓥} {⟨-2⟩} {A} {P} i g x = refl _
Trunc-ind'-β {𝓤} {𝓥} {S n} {A} {P} i g x = refl _


open import Ch7.3-Truncations-safe public

instance
  tc : Truncations
  Truncations.Truncation tc = Trunc
  Truncations.∣ tc ∣ = [_]
  Truncations.∥∥-Tlevel tc = Trunc-Tlevel
  Truncations.∥∥-induction tc = Trunc-ind'
  Truncations.∣∣-prop-β tc {𝓤} {𝓥} {⟨-2⟩} {A} {P} i g a = refl _
  Truncations.∣∣-prop-β tc {𝓤} {𝓥} {S n} {A} {P} i g a = refl _


{- The results that follow are also proved for the general case (i.e. no judgmental β-rule) in Ch7.3-Truncations-safe. -}

private

  -- Corollary: recursion principle.

  Trunc-rec : {n : Tlevel} {A : 𝓤 ̇} {B : 𝓥 ̇} → is n type B → (A → B) → Trunc n A → B
  Trunc-rec i g = Trunc-ind' (λ - → i) g

  Trunc-rec-β : {n : Tlevel} {A : 𝓤 ̇} {B : 𝓥 ̇} (i : is n type B) (g : A → B) → Trunc-rec i g ∘ [_] ∼ g
  Trunc-rec-β {𝓤} {𝓥} {⟨-2⟩} {A} {B} i g x = refl _
  Trunc-rec-β {𝓤} {𝓥} {S n} {A} {B} i g x = refl _

  -- Corollary: uniqueness principle for functions out of n-truncations.

  Trunc-uniqueness-pple : {n : Tlevel} {A : 𝓤 ̇} {B : 𝓥 ̇} → is n type B → {g g' : Trunc n A → B} → g ∘ [_] ∼ g' ∘ [_] → g ∼ g'
  Trunc-uniqueness-pple {𝓤} {𝓥} {n} {A} {B} i {g} {g'} f = Trunc-ind' (λ x → Tlevel-is-cumulative i (g x) (g' x)) f


  -- Lemma 7.3.3 (Universal property of truncations).

  module Trunc-UMP {n : Tlevel} (A : 𝓤 ̇) {B : 𝓥 ̇} (i : is n type B) where

    ϕ : (Trunc n A → B) → (A → B)
    ϕ f = f ∘ [_]

    ψ : (A → B) → Trunc n A → B
    ψ = Trunc-rec i

    α : ϕ ∘ ψ ∼ id
    α g = funext (Trunc-rec-β i g)

    β : ψ ∘ ϕ ∼ id
    β f = funext (Trunc-uniqueness-pple i (Trunc-rec-β i (f ∘ [_])))

    equiv : (Trunc n A → B) ≃ (A → B)
    equiv = ϕ , (qinv-to-isequiv {A = Trunc n A → B} {A → B} {ϕ} (ψ , α , β))


  -- Truncation is functorial

  Trunc-map : (n : Tlevel) {A : 𝓤 ̇} {B : 𝓥 ̇} → (A → B) → Trunc n A → Trunc n B
  Trunc-map n {A} {B} f = Trunc-rec Trunc-Tlevel ([_] ∘ f)

  Trunc-∘ : {n : Tlevel} {A : 𝓤 ̇} {B : 𝓥 ̇} {C : 𝓦 ̇} (f : A → B) (g : B → C) → Trunc-map n (g ∘ f) ∼ Trunc-map n g ∘ Trunc-map n f
  Trunc-∘ {𝓤} {𝓥} {𝓦} {⟨-2⟩} {A} {B} {C} f g = Trunc-uniqueness-pple Trunc-Tlevel (hrefl _)
  Trunc-∘ {𝓤} {𝓥} {𝓦} {S n} {A} {B} {C} f g = Trunc-uniqueness-pple Trunc-Tlevel (hrefl _)

  Trunc-𝑖𝑑 : {n : Tlevel} (A : 𝓤 ̇) → Trunc-map n (𝑖𝑑 A) ∼ 𝑖𝑑 (Trunc n A)
  Trunc-𝑖𝑑 {𝓤} {⟨-2⟩} A = Trunc-uniqueness-pple Trunc-Tlevel (hrefl _)
  Trunc-𝑖𝑑 {𝓤} {S n} A = Trunc-uniqueness-pple Trunc-Tlevel (hrefl _)


  -- [_] is natural

  []-nat : (n : Tlevel) {A : 𝓤 ̇} {B : 𝓥 ̇} (f : A → B) (a : A) → Trunc-map n f [ a ] ≡ [ f a ]
  []-nat ⟨-2⟩ f a = refl _
  []-nat (S n) f a = refl _


  -- Lemma 7.3.5 (Higher functoriality of Trunc)

  Trunc-∼ : (n : Tlevel) {A : 𝓤 ̇} {B : 𝓥 ̇} {f g : A → B} → f ∼ g → Trunc-map n f ∼ Trunc-map n g
  Trunc-∼ ⟨-2⟩ {A} {B} {f} {g} h = Trunc-ind' (λ x → Tlevel-is-cumulative Trunc-Tlevel _ _) λ a → ap [_] (h a)
  Trunc-∼ (S n) {A} {B} {f} {g} h = Trunc-ind' (λ x → Tlevel-is-cumulative Trunc-Tlevel _ _) λ a → ap [_] (h a)

  Trunc-∼-is-ap-[] : (n : Tlevel) {A : 𝓤 ̇} {B : 𝓥 ̇} {f g : A → B} (h : f ∼ g) (a : A) → []-nat n f a ⁻¹ ∙ Trunc-∼ n h [ a ] ∙ []-nat n g a ≡ ap [_] (h a)
  Trunc-∼-is-ap-[] ⟨-2⟩ h a = ru _ ⁻¹ ∙ lu _ ⁻¹
  Trunc-∼-is-ap-[] (S n) h a = ru _ ⁻¹ ∙ lu _ ⁻¹


  -- Corollary 7.3.7 (A is n-type iff [_] : A → Trunc n A is an equivalence).

  has-Tlevel-≃-[]-is-equiv : (n : Tlevel) (A : 𝓤 ̇) → is n type A ≃ isequiv ([_] {𝓤} {n} {A}) 
  has-Tlevel-≃-[]-is-equiv {𝓤} ⟨-2⟩ A = ⇔-to-≃ (Tlevel-is-predicate _ _) (ishae-is-Prop _)
    ((λ i → qinv-to-isequiv {f = [_] {𝓤} {⟨-2⟩} {A}} (Trunc-rec i id , Trunc-uniqueness-pple Trunc-Tlevel (hrefl _) , hrefl _)) ,
    λ i → ≃-preserves-Tlevel ⟨-2⟩ (Trunc ⟨-2⟩ A) A (≃-sym ([_] , i)) Trunc-Tlevel)  
  has-Tlevel-≃-[]-is-equiv {𝓤} (S n) A = ⇔-to-≃  (Tlevel-is-predicate _ _) (ishae-is-Prop _)
    ((λ i → qinv-to-isequiv {f = [_] {𝓤} {S n} {A}} (Trunc-rec i id , Trunc-uniqueness-pple Trunc-Tlevel (hrefl _) , hrefl _)) ,
    λ i → ≃-preserves-Tlevel (S n) (Trunc (S n) A) A (≃-sym ([_] , i)) Trunc-Tlevel)


  -- Theorem 7.3.8: see Ch7.3-Truncations-safe.


  -- Theorem 7.3.9 (Truncation preserves Σ).

  module Trunc-preserves-Σ where

    ϕ : (n : Tlevel) {A : 𝓤 ̇} (P : A → 𝓥 ̇) → Trunc n (Σ (Trunc n ∘ P)) → Trunc n (Σ P)
    ϕ n P = Trunc-rec Trunc-Tlevel (Σ-induction λ a → Trunc-rec Trunc-Tlevel (λ u → [ (a , u) ]))

    ψ : (n : Tlevel) {A : 𝓤 ̇} (P : A → 𝓥 ̇) → Trunc n (Σ P) → Trunc n (Σ (Trunc n ∘ P))
    ψ n P = Trunc-rec Trunc-Tlevel (Σ-induction λ a u → [ (a , [ u ]) ]) 

    H : (n : Tlevel) {A : 𝓤 ̇} (P : A → 𝓥 ̇) → ϕ n P ∘ ψ n P ∼ id
    H ⟨-2⟩ P = Trunc-uniqueness-pple Trunc-Tlevel (hrefl _)
    H (S n) P = Trunc-uniqueness-pple Trunc-Tlevel (hrefl _)

    K : (n : Tlevel) {A : 𝓤 ̇} (P : A → 𝓥 ̇) → ψ n P ∘ ϕ n P ∼ id
    K ⟨-2⟩ P = Trunc-uniqueness-pple Trunc-Tlevel (Σ-induction (λ a → Trunc-uniqueness-pple Trunc-Tlevel (hrefl _)))
    K (S n) P = Trunc-uniqueness-pple Trunc-Tlevel (Σ-induction (λ a → Trunc-uniqueness-pple Trunc-Tlevel (hrefl _)))

    equiv : (n : Tlevel) {A : 𝓤 ̇} (P : A → 𝓥 ̇) → Trunc n (Σ (Trunc n ∘ P)) ≃ Trunc n (Σ P)
    equiv n P = ϕ n P , qinv-to-isequiv (ψ n P , H n P , K n P)


-- TO DO: 7.3.12-14.

-- TO DO: constrain funext and univalence assumptions.


-- -- Theorem 7.3.12 (Path spaces of truncations).

-- module path-space-Trunc (n : Tlevel) {A : 𝓤 ̇} (x y : A) where

--   Trunc-≡ : Trunc n (x ≡ y) → Id (Trunc (S n) A) [ x ] [ y ]
--   Trunc-≡ = Trunc-rec (Trunc-Tlevel [ x ] [ y ]) (ap [_])

--   P : Trunc (S n) A → Trunc (S n) A → n Type 𝓤
--   P = Trunc-rec (→-preserves-Tlevel _ _ _ (Tlevel-Type-is-of-next-Tlevel n)) (λ x → Trunc-rec (Tlevel-Type-is-of-next-Tlevel n) λ y → (Trunc n (x ≡ y) , Trunc-Tlevel))

--   P₁ : Trunc (S n) A → Trunc (S n) A → 𝓤 ̇
--   P₁ u v = pr₁ (P u v)

--   P₂ : (u v : Trunc (S n) A) → is n type (P₁ u v)
--   P₂ u v = pr₂ (P u v)

--   decode : (u v : Trunc (S n) A) → P₁ u v → u ≡ v
--   decode = {!!}

-- --Trunc-ind (λ u → Π-preserves-Tlevel _ _ _ (λ v → →-preserves-Tlevel _ _ _ (Tlevel-is-cumulative _ _ (Trunc-Tlevel _ _)))) λ x → Trunc-ind (λ v → →-preserves-Tlevel _ _ _ (Tlevel-is-cumulative _ _ (Trunc-Tlevel _ _))) λ y p → {!!} -- Definitional equality is becoming necessary...


-- -- Lemma 7.3.15: see Ch7.3-Truncations-safe.


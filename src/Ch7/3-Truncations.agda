{-# OPTIONS --without-K --exact-split --rewriting #-}

open import Ch1.Type-theory
open import Ch2.Homotopy-type-theory
open import Ch3.Sets-and-logic
open import Ch4.Equivalences
open import Ch6.2-Induction-pples-and-dependent-paths
open import Ch6.5-Suspensions
open import Ch7.1-Definition-of-n-types
open import Ch7.2-UIP-and-Hedberg's-theorem

module Ch7.3-Truncations where

module truncations-as-HITs where

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

  Trunc-ind : {n : Tlevel} {A : 𝓤 ̇} (P : Trunc n A → 𝓥 ̇) (g : Π (P ∘ [_])) → Trunc-ind-data n A P g → Π P

  -- (iv) Computation rule for Trunc-ind ⟨-2⟩

  Trunc-ind-β : (n : Tlevel) (A : 𝓤 ̇) (P : Trunc n A → 𝓥 ̇) (g : Π (P ∘ [_])) (d : Trunc-ind-data n A P g) (a : A) →  Trunc-ind P g d [ a ] ↦ g a

  {-# REWRITE Trunc-ind-β #-}

Trunc-ind-comp : (n : Tlevel) (A : 𝓤 ̇) (P : Trunc n A → 𝓥 ̇) (g : Π (P ∘ [_])) (d : Trunc-ind-data n A P g) →  Trunc-ind P g d ∘ [_] ∼ g
Trunc-ind-comp n A P g d x = refl _


-- Lemma 7.3.1 (n-truncations are n-types).

Tlevel-of-Trunc : (n : Tlevel) (A : 𝓤 ̇) → is n type (Trunc n A)
Tlevel-of-Trunc ⟨-2⟩ A = hub , spoke ⟨-2⟩
Tlevel-of-Trunc (S n) A = pr₁ (≃-sym (Tlevel-in-terms-of-Map⊙ n (Trunc (S n) A))) (λ b → ((λ x → b) , (refl b)) , (Σ-induction λ r p → (dpair-≡ (q r b p , (transport-fun-ap (base (to-ℕ n)) b (q r b p) p ∙ (ap (λ - → - ⁻¹ ∙ p) (happly-β _ _ (λ x → spoke (S n) r x ∙ spoke (S n) r (base (to-ℕ n)) ⁻¹ ∙ p) (base (to-ℕ n)) ∙ (rinv _ ∙ᵣ p) ∙ lu _ ⁻¹) ∙ linv p)))) ⁻¹)) where
  q : (r : Sphere (to-ℕ n) → Trunc (S n) A) (b : Trunc (S n) A) (p : r (base (to-ℕ n)) ≡ b) → r ≡ λ x → b
  q r b p = funext _ _ λ x → spoke (S n) r x ∙ spoke (S n) r (base (to-ℕ n)) ⁻¹ ∙ p


-- Theorem 7.3.2 (Better induction principle for truncations)

Trunc-ind' : {n : Tlevel} {A : 𝓤 ̇} (P : Trunc n A → 𝓥 ̇) → ((x : Trunc n A) → is n type (P x)) → Π (P ∘ [_]) → Π P
Trunc-ind' {𝓤} {𝓥} {⟨-2⟩} {A} P i g = Trunc-ind {𝓤} {𝓥} {⟨-2⟩} {A} P g (
  (pr₁ (i hub)) ,
  (λ x u → pr₂ (pr₁ (isContr-iff-is-inhabited-Prop _) (i x)) _ _)
  )
Trunc-ind' {𝓤} {𝓥} {S n} {A} P i g = Trunc-ind {𝓤} {𝓥} {S n} {A} P g (u , v)
  where
  t : (r : Sphere (to-ℕ n) → Trunc (S n) A) (r' : (x : Sphere (to-ℕ n)) → P (r x)) → Sphere (to-ℕ n) → P (hub r)
  t r r' = λ x → transport P (spoke (S n) r x) (r' x)
  u : (r : Sphere (to-ℕ n) → Trunc (S n) A) (r' : (x : Sphere (to-ℕ n)) → P (r x)) → P (hub r)
  u r r' = pr₁ (hub-and-spokes n (P (hub r)) (i (hub r)) (t r r'))
  v : (r : Sphere (to-ℕ n) → Trunc (S n) A) (r' : (x : Sphere (to-ℕ n)) → P (r x)) (x : Sphere (to-ℕ n)) → t r r' x ≡ u r r'
  v r r' = pr₂ (hub-and-spokes n (P (hub r)) (i (hub r)) (t r r'))
  
-- Computation rule: we only get definitional equality after pattern-matching on n.

Trunc-ind'-β : {n : Tlevel} {A : 𝓤 ̇} (P : Trunc n A → 𝓥 ̇) (i : (x : Trunc n A) → is n type (P x)) (g : Π (P ∘ [_])) → Trunc-ind' P i g ∘ [_] ∼ g
Trunc-ind'-β {𝓤} {𝓥} {⟨-2⟩} {A} P i g x = refl _
Trunc-ind'-β {𝓤} {𝓥} {S n} {A} P i g x = refl _

-- Corollary: recursion principle.

Trunc-rec : {n : Tlevel} {A : 𝓤 ̇} (B : 𝓥 ̇) → is n type B → (A → B) → Trunc n A → B
Trunc-rec B i g = Trunc-ind' (λ - → B) (λ - → i) g

Trunc-rec-β : {n : Tlevel} {A : 𝓤 ̇} {B : 𝓥 ̇} (i : is n type B) (g : A → B) → Trunc-rec B i g ∘ [_] ∼ g
Trunc-rec-β {𝓤} {𝓥} {⟨-2⟩} {A} {B} i g x = refl _
Trunc-rec-β {𝓤} {𝓥} {S n} {A} {B} i g x = refl _

-- Corollary: uniqueness principle for functions out of n-truncations.

Trunc-uniqueness-pple : {n : Tlevel} {A : 𝓤 ̇} {B : 𝓥 ̇} → is n type B → (g g' : Trunc n A → B) → g ∘ [_] ∼ g' ∘ [_] → g ≡ g'
Trunc-uniqueness-pple {𝓤} {𝓥} {n} {A} {B} i g g' f = funext g g' (Trunc-ind' (λ x → g x ≡ g' x) (λ x → cumulativity-of-Tlevels n B i (g x) (g' x)) f)


-- Lemma 7.3.3 (Universal property of truncations).

module Trunc-UMP {n : Tlevel} (A : 𝓤 ̇) {B : 𝓥 ̇} (i : is n type B) where

  ϕ : (Trunc n A → B) → (A → B)
  ϕ f = f ∘ [_]

  ψ : (A → B) → Trunc n A → B
  ψ = Trunc-rec B i

  α : ϕ ∘ ψ ∼ id
  α g = funext _ _ (Trunc-rec-β i g)
  
  β : ψ ∘ ϕ ∼ id
  β f = Trunc-uniqueness-pple i _ _ (Trunc-rec-β i (f ∘ [_]))

  equivalence : (Trunc n A → B) ≃ (A → B)
  equivalence = ϕ , (qinv-to-isequiv {A = Trunc n A → B} {A → B} {ϕ} (ψ , α , β))


-- Truncation is functorial

fun-Trunc : (n : Tlevel) {A : 𝓤 ̇} {B : 𝓥 ̇} → (A → B) → Trunc n A → Trunc n B
fun-Trunc n {A} {B} f = Trunc-rec (Trunc n B) (Tlevel-of-Trunc n B) ([_] ∘ f)

fun-Trunc-∘ : {n : Tlevel} {A : 𝓤 ̇} {B : 𝓥 ̇} {C : 𝓦 ̇} (f : A → B) (g : B → C) → fun-Trunc n (g ∘ f) ≡ fun-Trunc n g ∘ fun-Trunc n f
fun-Trunc-∘ {𝓤} {𝓥} {𝓦} {⟨-2⟩} {A} {B} {C} f g = Trunc-uniqueness-pple (Tlevel-of-Trunc ⟨-2⟩ C) _ _ (hrefl _)
fun-Trunc-∘ {𝓤} {𝓥} {𝓦} {S n} {A} {B} {C} f g = Trunc-uniqueness-pple (Tlevel-of-Trunc (S n) C) _ _ (hrefl _)

fun-Trunc-𝑖𝑑 : {n : Tlevel} (A : 𝓤 ̇) → fun-Trunc n (𝑖𝑑 A) ≡ 𝑖𝑑 (Trunc n A)
fun-Trunc-𝑖𝑑 {𝓤} {⟨-2⟩} A = Trunc-uniqueness-pple (Tlevel-of-Trunc ⟨-2⟩ A) _ _ (hrefl _)
fun-Trunc-𝑖𝑑 {𝓤} {S n} A = Trunc-uniqueness-pple (Tlevel-of-Trunc (S n) A) _ _ (hrefl _)


-- [_] is natural

[]-nat : (n : Tlevel) {A : 𝓤 ̇} {B : 𝓥 ̇} (f : A → B) (a : A) → fun-Trunc n f [ a ] ≡ [ f a ]
[]-nat ⟨-2⟩ f a = refl _
[]-nat (S n) f a = refl _


-- Lemma 7.3.5 (Higher functoriality of Trunc)

h-Trunc : (n : Tlevel) {A : 𝓤 ̇} {B : 𝓥 ̇} {f g : A → B} → f ∼ g → fun-Trunc n f ∼ fun-Trunc n g
h-Trunc ⟨-2⟩ {A} {B} {f} {g} h = Trunc-ind' (λ x → fun-Trunc ⟨-2⟩ f x ≡ fun-Trunc ⟨-2⟩ g x) (λ x → cumulativity-of-Tlevels ⟨-2⟩ (Trunc ⟨-2⟩ B) (Tlevel-of-Trunc ⟨-2⟩ B) _ _) λ a → ap [_] (h a)
h-Trunc (S n) {A} {B} {f} {g} h = Trunc-ind' (λ x → fun-Trunc (S n) f x ≡ fun-Trunc (S n) g x) (λ x → cumulativity-of-Tlevels (S n) (Trunc (S n) B) (Tlevel-of-Trunc (S n) B) _ _) λ a → ap [_] (h a)

h-Trunc-is-ap-[] : (n : Tlevel) {A : 𝓤 ̇} {B : 𝓥 ̇} {f g : A → B} (h : f ∼ g) (a : A) → []-nat n f a ⁻¹ ∙ h-Trunc n h [ a ] ∙ []-nat n g a ≡ ap [_] (h a)
h-Trunc-is-ap-[] ⟨-2⟩ h a = ru _ ⁻¹ ∙ lu _ ⁻¹
h-Trunc-is-ap-[] (S n) h a = ru _ ⁻¹ ∙ lu _ ⁻¹


-- Corollary 7.3.7 (A is n-type iff [_] : A → Trunc n A is an equivalence).

has-Tlevel-≃-[]-is-equiv : (n : Tlevel) (A : 𝓤 ̇) → is n type A ≃ isequiv ([_] {𝓤} {n} {A}) 
has-Tlevel-≃-[]-is-equiv {𝓤} ⟨-2⟩ A = biimplication-to-≃ _ _ (Tlevel-is-predicate _ _) (ishae-is-Prop _)
  (λ i → qinv-to-isequiv {f = [_] {𝓤} {⟨-2⟩} {A}} (Trunc-rec _ i id , happly _ _ (Trunc-uniqueness-pple (Tlevel-of-Trunc ⟨-2⟩ A) _ _ (hrefl _)) , hrefl _))
  λ i → ≃-preserves-Tlevel ⟨-2⟩ (Trunc ⟨-2⟩ A) A (≃-sym ([_] , i)) (Tlevel-of-Trunc ⟨-2⟩ A)
has-Tlevel-≃-[]-is-equiv {𝓤} (S n) A = biimplication-to-≃ _ _ (Tlevel-is-predicate _ _) (ishae-is-Prop _)
  (λ i → qinv-to-isequiv {f = [_] {𝓤} {S n} {A}} (Trunc-rec _ i id , happly _ _ (Trunc-uniqueness-pple (Tlevel-of-Trunc (S n) A) _ _ (hrefl _)) , hrefl _))
  λ i → ≃-preserves-Tlevel (S n) (Trunc (S n) A) A (≃-sym ([_] , i)) (Tlevel-of-Trunc (S n) A)


-- Theorem 7.3.8 ([_] preserves finite products).



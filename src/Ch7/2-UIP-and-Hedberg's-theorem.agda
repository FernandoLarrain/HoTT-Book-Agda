{-# OPTIONS --without-K --exact-split #-}

open import Ch1.Type-theory
open import Ch2.Homotopy-type-theory
open import Ch3.Sets-and-logic
open import Ch4.Equivalences
open import Ch7.1-Definition-of-n-types

module Ch7.2-UIP-and-Hedberg's-theorem where

-- Theorem 7.2.1 (Sets are precisely the types satisfying Axiom K).

_satisfies-Axiom-K : (X : 𝓤 ̇) → 𝓤 ̇
X satisfies-Axiom-K = (x : X) (p : x ≡ x) → p ≡ refl x 

isSet-iff-Axiom-K : (X : 𝓤 ̇) → (isSet X → X satisfies-Axiom-K) × (X satisfies-Axiom-K → isSet X)
isSet-iff-Axiom-K X = sufficiency , necessity where
  sufficiency : isSet X → X satisfies-Axiom-K
  sufficiency f x p = f x x p (refl x)
  necessity : (X satisfies-Axiom-K → isSet X)
  necessity k x .x p (refl .x) = k x p


-- Theorem 7.2.2 (A useful way to prove "sethood").

module least-reflexive-rel (X : 𝓤 ̇) (R : X → X → 𝓤 ̇) ( mere-rel : (x y : X) → isProp (R x y)) (ρ : (x : X) → R x x) (f : (x y : X) → R x y → x ≡ y) where

  implies-is-Set : isSet X
  implies-is-Set = pr₂ (isSet-iff-Axiom-K X) (λ x p → ∙ₗ-inv (f x x (ρ x)) _ _ (firstly x p (ρ x) ∙ (ru _))) where
    firstly : (x : X) (p : x ≡ x) (r : R x x)  → f x x r ∙ p ≡ f x x r
    firstly x p r = transport-post-∙ X x _ _ p (f x x r) ⁻¹ ∙ pr₁ (dfunext.equiv (R x) (Id X x) _ _ p (f x x) (f x x)) (apd (f x) p) r ∙ ap (f x x) (mere-rel x x _ _) 

  is-≡ : ((x y : X) → R x y ≃ (x ≡ y))
  is-≡ x y = (f x y) , (pr₂ (fiberwise-≃-iff-total-≃.Hae (f x)) (map-between-Contrs-is-equiv (total (f x)) dom-is-Contr codom-is-Contr) y)
    where
    codom-is-Contr : isContr (Σ λ y → x ≡ y)
    codom-is-Contr = free-right-endpt-is-Contr _ _
    dom-is-Contr : isContr (Σ λ y → R x y)
    dom-is-Contr = (x , (ρ x)) , Σ-induction (λ y H → Σ-over-predicate X (R x) (mere-rel x) _ _ (f x y H))


  biimplication : (isSet X → ((x y : X) → R x y ≃ (x ≡ y))) × (((x y : X) → R x y ≃ (x ≡ y)) → isSet X)
  biimplication  = sufficiency , necessity
    where
    sufficiency : isSet X → (x y : X) → R x y ≃ (x ≡ y)
    sufficiency X-is-Set x y = biimplication-to-≃ _ _ (mere-rel x y) (X-is-Set x y) (f x y) (ℍ x (λ y p → R x y) (ρ x) y)
    necessity : ((x y : X) → R x y ≃ (x ≡ y)) → isSet X
    necessity g x y = ≃-preserves-Props (R x y) _ (g x y) (mere-rel x y)


-- Corollary 7.2.3 (DNE for _≡_ implies sethood).

dne-≡-to-isSet : (X : 𝓤 ̇) → ((x y : X) → ¬ (¬ (x ≡ y)) → x ≡ y) → isSet X
dne-≡-to-isSet X dne = least-reflexive-rel.implies-is-Set X (λ x y → ¬ (¬ (x ≡ y))) (λ x y u v → funext _ _ λ z → !𝟘 _ (u z)) (λ x u → u (refl x)) dne


-- Lemma 7.2.4 (LEM implies DNE)

lem-to-dne : (A : 𝓤 ̇) → (A + (¬ A)) → ¬ (¬ A) → A
lem-to-dne A (inl x) = λ y → x
lem-to-dne A (inr x) = λ y → !𝟘 _ (y x)


-- Theorem 7.2.5 (Hedberg).

decidable-equality-implies-isSet : (X : 𝓤 ̇) → decidable-equality X → isSet X
decidable-equality-implies-isSet X de = dne-≡-to-isSet X λ x y → lem-to-dne _ (de x y)


-- Theorem 7.2.6 (ℕ has decidable equality and, therefore, is a set).

ℕ-has-decidable-equality : decidable-equality ℕ
ℕ-has-decidable-equality zero zero = inl (refl 0)
ℕ-has-decidable-equality zero (succ m) = inr λ p → succ-is-not-0 m (p ⁻¹)
ℕ-has-decidable-equality (succ n) zero = inr (succ-is-not-0 n)
ℕ-has-decidable-equality (succ n) (succ m) = +-recursion (λ p → inl (ap succ p)) (λ f → inr λ p → f (succ-is-injective n m p)) (ℕ-has-decidable-equality n m)



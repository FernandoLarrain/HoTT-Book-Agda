{-# OPTIONS --without-K --exact-split --safe #-}

open import Ch1.Type-theory
open import Ch2.Homotopy-type-theory
open import Ch3.Sets-and-logic
open import Ch4.Equivalences
open import Ch7.1-Definition-of-n-types

module Ch7.2-UIP-and-Hedberg's-theorem-safe where


-- Theorem 7.2.1 (Sets are precisely the types satisfying Axiom K).

Axiom-K : (X : 𝓤 ̇) → 𝓤 ̇
Axiom-K X = (x : X) (p : x ≡ x) → p ≡ refl x

module _ ⦃ fe : FunExt ⦄ where

  isSet-≃-Axiom-K : (X : 𝓤 ̇) → isSet X ≃ Axiom-K X
  isSet-≃-Axiom-K X = retraction-of-Prop-to-≃ (isSet-is-Prop _) (sufficiency , necessity , α)
    where
    sufficiency : isSet X → Axiom-K X
    sufficiency f x p = f x x p (refl x)
    necessity : (Axiom-K X → isSet X)
    necessity k x .x p (refl .x) = k x p
    α : sufficiency ∘ necessity ∼ id
    α k = funext λ x → funext λ p → isSet-to-is-⟨1⟩-type _ (necessity k) _ _ _ _ _ _

  Axiom-K-is-Prop : (X : 𝓤 ̇) → isProp (Axiom-K X)
  Axiom-K-is-Prop X = ≃-preserves-Props (isSet-≃-Axiom-K X) (isSet-is-Prop X)

  Axiom-K-≃-Contr-Ω : (X : 𝓤 ̇) → Axiom-K X ≃ ((x : X) → isContr (x ≡ x))
  Axiom-K-≃-Contr-Ω X = ⇔-to-≃ (Axiom-K-is-Prop _) (Π-preserves-Props _ λ x → isContr-is-Prop _) ((λ k x → refl x , λ p → k x p ⁻¹) , λ c x p → (pr₂ (c x) p) ⁻¹ ∙ pr₂ (c x) (refl x))
    

-- Theorem 7.2.2 (A useful way to prove "sethood").

module least-reflexive-rel ⦃ fe : FunExt ⦄ (X : 𝓤 ̇) (R : X → X → 𝓤 ̇) ( mere-rel : (x y : X) → isProp (R x y)) (ρ : (x : X) → R x x) (f : (x y : X) → R x y → x ≡ y) where

  implies-is-Set : isSet X
  implies-is-Set = pr₁ (≃-sym (isSet-≃-Axiom-K X)) (λ x p → ∙ₗ-inv (f x x (ρ x)) _ _ (firstly x p (ρ x) ∙ (ru _))) where
    firstly : (x : X) (p : x ≡ x) (r : R x x)  → f x x r ∙ p ≡ f x x r
    firstly x p r = transport-post-∙ p (f x x r) ⁻¹ ∙ pr₁ (dpath-funext.equiv (R x) (Id X x) p (f x x) (f x x)) (apd (f x) p) r ∙ ap (f x x) (mere-rel x x _ _) 

  is-≡ : ((x y : X) → R x y ≃ (x ≡ y))
  is-≡ x y = (f x y) , (pr₂ (fiberwise-≃-iff-total-≃.Hae (f x)) (map-between-Contrs-is-equiv (total (f x)) dom-is-Contr codom-is-Contr) y)
    where
    codom-is-Contr : isContr (Σ λ y → x ≡ y)
    codom-is-Contr = free-right-endpt-is-Contr _ _
    dom-is-Contr : isContr (Σ λ y → R x y)
    dom-is-Contr = (x , (ρ x)) , Σ-induction (λ y H → Σ-over-predicate (mere-rel x) (f x y H))


  equivalence : isSet X ≃ ((x y : X) → R x y ≃ (x ≡ y))
  equivalence  = ⇔-to-≃ (isSet-is-Prop _) (Π-preserves-Props _ (λ x → Π-preserves-Props _ λ y → ≃-to-Prop-is-Prop' _ _ (mere-rel x y))) (sufficiency , necessity)
    where
    sufficiency : isSet X → (x y : X) → R x y ≃ (x ≡ y)
    sufficiency X-is-Set x y = ⇔-to-≃ (mere-rel x y) (X-is-Set x y) (f x y , ℍ x (λ y p → R x y) (ρ x) y)
    necessity : ((x y : X) → R x y ≃ (x ≡ y)) → isSet X
    necessity g x y = ≃-preserves-Props (g x y) (mere-rel x y)


-- Corollary 7.2.3 (DNE for _≡_ implies sethood).

dne-≡-to-isSet : ⦃ fe : FunExt ⦄ (X : 𝓤 ̇) → ((x y : X) → ¬ (¬ (x ≡ y)) → x ≡ y) → isSet X
dne-≡-to-isSet X dne = least-reflexive-rel.implies-is-Set X (λ x y → ¬ (¬ (x ≡ y))) (λ x y u v → funext λ z → !𝟘 _ (u z)) (λ x u → u (refl x)) dne


-- Lemma 7.2.4 (LEM implies DNE)

lem-to-dne : (A : 𝓤 ̇) → (A + (¬ A)) → ¬ (¬ A) → A
lem-to-dne A (inl x) = λ y → x
lem-to-dne A (inr x) = λ y → !𝟘 _ (y x)


-- Theorem 7.2.5 (Hedberg).

decidable-equality-implies-isSet : ⦃ fe : FunExt ⦄ (X : 𝓤 ̇) → decidable-equality X → isSet X
decidable-equality-implies-isSet X de = dne-≡-to-isSet X λ x y → lem-to-dne _ (de x y)


-- Theorem 7.2.6 (ℕ has decidable equality and, therefore, is a set).

ℕ-has-decidable-equality : decidable-equality ℕ
ℕ-has-decidable-equality zero zero = inl (refl 0)
ℕ-has-decidable-equality zero (succ m) = inr λ p → succ-is-not-0 m (p ⁻¹)
ℕ-has-decidable-equality (succ n) zero = inr (succ-is-not-0 n)
ℕ-has-decidable-equality (succ n) (succ m) = +-recursion (λ p → inl (ap succ p)) (λ f → inr λ p → f (succ-is-injective n m p)) (ℕ-has-decidable-equality n m)


-- Theorem 7.2.7 (characterization of truncation level in terms of loop spaces).

Tlevel-in-terms-of-Ω : ⦃ fe : FunExt ⦄ (n : Tlevel) (X : 𝓤 ̇) → is S (S n) type X ≃ ((x : X) → is S n type (x ≡ x))

-- (i) Lemma 7.2.8 (can assume type is inhabited to show it is S n type.)

inhabited-type-assum : (n : Tlevel) (X : 𝓤 ̇) → (X → is S n type X) → is S n type X
inhabited-type-assum n X f x x' = f x x x'

-- (ii) Proof of thm:

Tlevel-in-terms-of-Ω n X = ⇔-to-≃ (Tlevel-is-predicate _ _) (Π-preserves-Props _ (λ x → Tlevel-is-predicate _ _)) (sufficiency , necessity) where
  sufficiency : is S (S n) type X → ((x : X) → is S n type (x ≡ x))
  sufficiency f x = f x x
  necessity : ((x : X) → is S n type (x ≡ x)) → is S (S n) type X
  necessity f x x' = inhabited-type-assum _ _ (𝕁 X (λ x x' p → is S n type (x ≡ x')) f _ _)


-- Quantification over constant predicate

∀-over-constant-pred : ⦃ fe : FunExt ⦄ {A : 𝓤 ̇} {B : 𝓥 ̇} → A → isProp B → (∀ (a : A) → B) ≃ B
∀-over-constant-pred a₀ B-is-Prop = (λ f → f a₀) , (qinv-to-isequiv (
  (λ b a → b) ,
  (λ b → refl b) ,
  (λ f → funext (λ a → B-is-Prop _ _))
  ))


-- Theorem 7.2.9 (generalized Axiom K).

generalized-Axiom-K : ⦃ fe : FunExt ⦄ ⦃ univ : Univalence ⦄ (n : Tlevel) (A : 𝓤 ̇) → is (S n) type A ≃ ((a : A) → isContr (pr₁ (Ω^ (to-ℕ n) (A , a))))
generalized-Axiom-K ⟨-2⟩ A = ≃-sym (isProp-≃-is-⟨-1⟩-type A) ● isProp-≃-inhabited-to-isContr A 
generalized-Axiom-K (S ⟨-2⟩) A = ≃-sym (isSet-≃-is-⟨0⟩-type A) ● (isSet-≃-Axiom-K A ● Axiom-K-≃-Contr-Ω A)
generalized-Axiom-K (S (S n)) A =
  is S (S (S n)) type A
    ≃⟨ Tlevel-in-terms-of-Ω _ _ ⟩
  ((a : A) → is S (S n) type (a ≡ a))
    ≃⟨ Π-preserves-family-≃ (λ a → generalized-Axiom-K (S n) (a ≡ a)) ⟩
  ((a : A) (p : a ≡ a) → isContr (pr₁ (Ω^ (to-ℕ (S n)) ((a ≡ a) , p))))
    ≃⟨ Π-preserves-family-≃ (λ a → Π-preserves-family-≃ λ p → idtoeqv (ap (λ - → isContr (pr₁ (Ω^ (to-ℕ n) -))) (aux-identity a p))) ⟩
  ((a : A) (p : a ≡ a) → isContr (pr₁ (Ω^ (to-ℕ n) ((refl a ≡ refl a) , refl (refl a)))))
    ≃⟨ ((Π-preserves-family-≃ λ a → ∀-over-constant-pred (refl a) (isContr-is-Prop _))) ⟩
  ((a : A) → isContr (pr₁ (Ω^ (to-ℕ n) ((refl a ≡ refl a) , refl (refl a))))) ■
  where
    aux-identity : (a : A) (p : a ≡ a) → Ω ((a ≡ a) , p) ≡ Ω^ 2 (A , a)
    aux-identity a p = dpair-≡ (
      ua (
        (ap (λ r → r ∙ p ⁻¹) {p} {p}) , ap-of-equiv-is-equiv (qinv-to-isequiv (qinv-post-∙ a (p ⁻¹))) p p  ●
        post-∙-≃ _ (rinv p) ●
        pre-∙-≃ _ (rinv p ⁻¹)
      ) ,
      (idtoeqv-β _ (refl p) ∙ (ap (rinv p ⁻¹ ∙_) (lu (rinv p)) ⁻¹ ∙ linv (rinv p)))
      )



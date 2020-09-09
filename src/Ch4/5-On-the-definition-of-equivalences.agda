{-# OPTIONS --without-K --exact-split --safe #-}

open import Ch1.Type-theory
open import Ch2.Homotopy-type-theory
open import Ch3.Sets-and-logic
open import Ch4.2-Half-adjoint-equivalences
open import Ch4.3-Bi-invertible-maps
open import Ch4.4-Contractible-fibers

module Ch4.5-On-the-definition-of-equivalences where

{- Note: Up to this point, the official definition of equivalence is bi-invertible maps. From now on , it is half-adjoint equivalences. The code works with both definitions until Ch4.4-Contractible-fibers. -}

-- ishae contains the most directly useful data, as can be seen from the following results, which extend exercise 2.17.

module _ ⦃ fe : FunExt ⦄ where

  Π-preserves-base-≃ : {A : 𝓤 ̇} {B : 𝓥 ̇} (P : B → 𝓦 ̇) (e : A ≃ B) → Π (P ∘ pr₁ e) ≃ Π P
  Π-preserves-base-≃ P (f , g , η , ε , τ) =
    (λ h b → transport P (ε b) (h (g b))) ,
    (qinv-to-ishae (
      (λ k a → k (f a)) ,
      (λ k → funext (λ b → apd k (ε b))) ,
      λ h → funext (λ a → ap (λ - → transport P - (h (g (f a)))) (τ a ⁻¹)∙ (transport-∘ P f (η a) (h (g (f a))) ⁻¹ ∙ apd h (η a)))
      )
    )

  Π-preserves-≃ : {A : 𝓤 ̇} {B : 𝓥 ̇} (P : A → 𝓦 ̇) (Q : B → 𝓣 ̇) (e : A ≃ B) → ((a : A) → P a ≃ Q (pr₁ e a)) → Π P ≃ Π Q
  Π-preserves-≃ P Q e t = Π-preserves-family-≃ t ● Π-preserves-base-≃ Q e  

  Π-preserves-base-≃' : {A : 𝓤 ̇} {B : 𝓥 ̇} (P : A → 𝓦 ̇) (e : A ≃ B) → Π P ≃ Π (P ∘ inv e)
  Π-preserves-base-≃' P e = ≃-sym (Π-preserves-base-≃ P (≃-sym e))

  Π-preserves-≃' : {A : 𝓤 ̇} {B : 𝓥 ̇} (P : A → 𝓦 ̇) (Q : B → 𝓣 ̇) (e : A ≃ B) → ((b : B) → P (inv e b) ≃ Q b) → Π P ≃ Π Q
  Π-preserves-≃' P Q e t = Π-preserves-base-≃' P e ● Π-preserves-family-≃ t

Σ-preserves-base-≃ : {A : 𝓤 ̇} {B : 𝓥 ̇} (P : B → 𝓦 ̇) (e : A ≃ B) → (Σ (P ∘ (pr₁ e)) ≃ Σ P) 
Σ-preserves-base-≃ P (f , g , η , ε , τ) =
  Σ-induction (λ a y → (f a) , y) ,
  (qinv-to-ishae (
    Σ-induction (λ b y → (g b) , (transport P (ε b ⁻¹) y)) ,
    Σ-induction (λ b y → dpair-≡ (ε b , (transport-∙ P (ε b ⁻¹) (ε b) y ∙ ap (λ - → transport P - y) (linv (ε b))))) ,
    Σ-induction (λ a y → dpair-≡ (η a , (transport-∘ P f (η a) _ ∙ (transport-∙ P (ε (f a) ⁻¹) (ap f (η a)) y ∙ ap (λ - → transport P - y) ((ε (f a) ⁻¹ ∙ₗ τ a) ∙ linv (ε (f a)))))))
    )
  )

Σ-preserves-≃ : {A : 𝓤 ̇} {B : 𝓥 ̇} (P : A → 𝓦 ̇) (Q : B → 𝓣 ̇) (e : A ≃ B) → ((a : A) → P a ≃ Q (pr₁ e a)) → Σ P ≃ Σ Q
Σ-preserves-≃ P Q e t = Σ-preserves-family-≃ t ● Σ-preserves-base-≃ Q e 

Σ-preserves-base-≃' : {A : 𝓤 ̇} {B : 𝓥 ̇} (P : A → 𝓦 ̇) (e : A ≃ B) → Σ P ≃ Σ (P ∘ inv e)
Σ-preserves-base-≃' P e = ≃-sym (Σ-preserves-base-≃ P (≃-sym e)) 

Σ-preserves-≃' : {A : 𝓤 ̇} {B : 𝓥 ̇} (P : A → 𝓦 ̇) (Q : B → 𝓣 ̇) (e : A ≃ B) → ((b : B) → P (inv e b) ≃ Q b) → Σ P ≃ Σ Q
Σ-preserves-≃' P Q e t = Σ-preserves-base-≃' P e ● Σ-preserves-family-≃ t


-- Groupoid laws for equivalences:

module _ ⦃ fe : FunExt ⦄ {A : 𝓤 ̇} {B : 𝓥 ̇} where

  ≃-ru : (e : A ≃ B) → e ● ≃-refl B ≡ e
  ≃-ru e = Σ-over-predicate (ishae-is-Prop {𝓤} {𝓥} {A} {B}) (refl _)

  ≃-lu : (e : A ≃ B) → ≃-refl A ● e ≡ e 
  ≃-lu e = Σ-over-predicate (ishae-is-Prop {𝓤} {𝓥} {A} {B}) (refl _)

  ≃-rinv : (e : A ≃ B) → e ● ≃-sym e ≡ ≃-refl A
  ≃-rinv (f , g , η , ε , τ) = Σ-over-predicate (ishae-is-Prop {𝓤} {𝓤} {A} {A}) (funext η)

  ≃-linv : (e : A ≃ B) → ≃-sym e ● e ≡ ≃-refl B
  ≃-linv (f , g , η , ε , τ) = Σ-over-predicate (ishae-is-Prop {𝓥} {𝓥} {B} {B}) (funext ε)

  ≃-sym-invol : (e : A ≃ B) → ≃-sym (≃-sym e) ≡ e
  ≃-sym-invol e = Σ-over-predicate (ishae-is-Prop {𝓤} {𝓥} {A} {B}) (refl _)

●-assoc : ⦃ fe : FunExt ⦄ {A : 𝓤 ̇} {B : 𝓥 ̇} {C : 𝓦 ̇} {D : 𝓣 ̇} (e : A ≃ B) (f : B ≃ C) (g : C ≃ D) → e ● (f ● g) ≡ e ● f ● g
●-assoc {𝓤} {𝓥} {𝓦} {𝓣} {A} {B} {C} {D} e f g = Σ-over-predicate (ishae-is-Prop {𝓤} {𝓣} {A} {D}) (refl _)

-- A related law

≃-distr : ⦃ fe : FunExt ⦄ {A : 𝓤 ̇} {B : 𝓥 ̇} {C : 𝓦 ̇} (e : A ≃ B) (f : B ≃ C) → ≃-sym (e ● f) ≡ ≃-sym f ● ≃-sym e
≃-distr {𝓤} {𝓥} {𝓦} {A} {B} {C} e f = Σ-over-predicate (ishae-is-Prop {𝓦} {𝓤} {C} {A}) (refl _)


-- ≃ preserves ≃

≃-preserves-left-≃ : ⦃ fe : FunExt ⦄ {A : 𝓤 ̇} (B : 𝓥 ̇) {A' : 𝓦 ̇} → A ≃ A' → (A ≃ B) ≃ (A' ≃ B)
≃-preserves-left-≃ {𝓤} {𝓥} {𝓦} {A} B {A'} e = (≃-sym e ●_) , qinv-to-isequiv {_} {_} {A ≃ B} {A' ≃ B} {≃-sym e ●_} ((e ●_) , (λ f → ●-assoc (≃-sym e) e f ∙ ap (_● f) (≃-linv e) ∙ ≃-lu f) , λ f → ●-assoc e (≃-sym e) f ∙ ap (_● f) (≃-rinv e) ∙ ≃-lu f)

≃-preserves-right-≃ : ⦃ fe : FunExt ⦄ (A : 𝓤 ̇) {B : 𝓥 ̇} {B' : 𝓦 ̇} → B ≃ B' → (A ≃ B) ≃ (A ≃ B')
≃-preserves-right-≃ {𝓤} {𝓥} {𝓦} A {B} {B'} e = (_● e) , (qinv-to-isequiv {_} {_} {A ≃ B} {A ≃ B'} {_● e} ((_● (≃-sym e)) , (λ f → ●-assoc f (≃-sym e) e ⁻¹ ∙ (ap (f ●_) (≃-linv e) ∙ ≃-ru f)) , λ f → ●-assoc f e (≃-sym e) ⁻¹ ∙ ap (f ●_) (≃-rinv e) ∙ ≃-ru f))


-- ≃-sym is its own quasi-inverse

qinv-≃-sym : ⦃ fe : FunExt ⦄ {A : 𝓤 ̇} {B : 𝓥 ̇} → qinv (≃-sym {𝓤} {𝓥} {A} {B})
qinv-≃-sym = ≃-sym , (λ e⁻¹ → Σ-over-predicate ishae-is-Prop (refl _)) , (λ e → Σ-over-predicate ishae-is-Prop (refl _))

≃-sym-≃ : ⦃ fe : FunExt ⦄ {A : 𝓤 ̇} {B : 𝓥 ̇} → (A ≃ B) ≃ (B ≃ A)
≃-sym-≃ = ≃-sym , qinv-to-isequiv qinv-≃-sym

-- Lemma 3.3.3 continued (logically equivalent propositions are equivalent).

module _ ⦃ fe : FunExt ⦄ where

-- (i) Equivalence to a proposition is a proposition

  ≃-to-Prop-is-Prop : (P : 𝓤 ̇ ) (Q : 𝓥 ̇ ) → isProp Q → isProp (P ≃ Q)
  ≃-to-Prop-is-Prop P Q Q-is-Prop = Σ-preserves-Props (→-preserves-Props _ _ Q-is-Prop) (λ f → ishae-is-Prop f )

-- (ii) (i) symmetrized

  ≃-to-Prop-is-Prop' : (P : 𝓤 ̇ ) (Q : 𝓥 ̇ ) → isProp P → isProp (P ≃ Q)
  ≃-to-Prop-is-Prop' P Q P-is-Prop = ≃-preserves-Props ≃-sym-≃ (≃-to-Prop-is-Prop _ _ P-is-Prop)

-- (iii) The lemma

  biimplication-of-Props-is-≃ : {P : 𝓤 ̇} {Q : 𝓥 ̇} → isProp P → isProp Q → (P ⇔ Q) ≃ (P ≃ Q)
  biimplication-of-Props-is-≃ P-is-Prop Q-is-Prop = ⇔-to-≃ (×-preserves-Props _ _ (→-preserves-Props _ _ Q-is-Prop) (→-preserves-Props _ _ P-is-Prop)) (≃-to-Prop-is-Prop _ _ Q-is-Prop) (⇔-to-≃ P-is-Prop Q-is-Prop , ≃-to-⇔)

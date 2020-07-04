{-# OPTIONS --without-K --exact-split #-}

open import Ch1.Type-theory
open import Ch2.1-Types-are-higher-groupoids
open import Ch2.2-Functions-are-functors
open import Ch2.3-Type-families-are-fibrations
open import Ch2.4-Homotopies-and-equivalences
open import Ch2.7-Σ-types
open import Ch2.9-Π-types-and-funext

module Ch2.10-Universes-and-univalence where


-- Lemma 2.10.1 (from identity to equivalence)

coe : {A B : 𝓤 ̇} → A ≡ B → A → B
coe = transport id

idtoeqv : (A B : 𝓤 ̇) → (A ≡ B) → (A ≃ B)
idtoeqv {𝓤} A B p =
  coe p ,
  qinv-to-isequiv (ℍ A (λ B p → qinv (coe p)) (qinv-𝑖𝑑 A) B p)


-- Axiom 2.10.3 (Univalence)

-- (i) Definition of univalence for a given universe

is-univalent : (𝓤 : Universe) → 𝓤 ⁺ ̇
is-univalent 𝓤 = (X Y : 𝓤 ̇ ) → isequiv (idtoeqv X Y)

-- (ii) Definition of global univalence

Univalence : 𝓤ω
Univalence = ∀ 𝓤 → is-univalent 𝓤

-- (iii) Postulating the axiom

postulate
  univ : Univalence


-- From equivalence to identity

ua : (A B : 𝓤 ̇ ) → (A ≃ B) → (A ≡ B)
ua {𝓤} A B = qinv₁ (isequiv-to-qinv (univ 𝓤 A B))
  

-- Computation rules for univalence

idtoeqv-β : (A B : 𝓤 ̇) → (f : A ≃ B) → coe (ua A B f) ∼ pr₁ f
idtoeqv-β {𝓤} A B f = happly _ (pr₁ f) (pr₁ (dpr-≡ (α f)))
  where
  α : (idtoeqv A B ∘ ua A B) ∼ id
  α = qinv₂ (isequiv-to-qinv (univ 𝓤 A B))

idtoeqv-β' : (A B : 𝓤 ̇) → (idtoeqv A B ∘ ua A B) ∼ id
idtoeqv-β' {𝓤} A B = qinv₂ (isequiv-to-qinv (univ 𝓤 A B))

idtoeqv-β'' : (A B : 𝓤 ̇) → (idtoeqv A B ∘ ua A B) ≡ id
idtoeqv-β'' {𝓤} A B = funext _ _ (idtoeqv-β' A B)


-- Uniqueness rule for univalence

idtoeqv-η : (A B : 𝓤 ̇) → (ua A B ∘ idtoeqv A B) ∼ id
idtoeqv-η {𝓤} A B = qinv₃ (isequiv-to-qinv (univ 𝓤 A B))


-- Functoriality of ua  
  
type-refl : (A : 𝓤 ̇) → refl A ≡ ua A A (≃-refl A)
type-refl A = (idtoeqv-η _ _ (refl A)) ⁻¹ ∙ ap (ua A A) (refl _)

type-sym : (A B : 𝓤 ̇) (f : A ≃ B) → ua A B f ⁻¹ ≡ ua B A (≃-sym f)
type-sym {𝓤} A B f = lemma _ _ (ua A B f) ∙ ap (ua B A ∘ ≃-sym) (idtoeqv-β' A B f)
  where
  lemma : (A B : 𝓤 ̇) (p : A ≡ B) → p ⁻¹ ≡ ua B A (≃-sym (idtoeqv A B p))
  lemma A .A (refl .A) = type-refl A
  
type-trans : (A B C : 𝓤 ̇) (e : A ≃ B) (f : B ≃ C) → ua A B e ∙ ua B C f ≡ ua A C (e ● f)
type-trans A B C e f = lemma _ _ _ (ua A B e) (ua B C f) ∙ (ap (λ - →  ua A C (- ● idtoeqv B C (ua B C f))) (idtoeqv-β' A B e) ∙ ap (λ - → ua A C (e ● -)) (idtoeqv-β' B C f))
  where
  lemma : (A B C : 𝓤 ̇) (p : A ≡ B) (q : B ≡ C) → p ∙ q ≡ ua A C ((idtoeqv A B p) ● (idtoeqv B C q))
  lemma .B B .B (refl .B) (refl .B) = type-refl B


-- Lemma 2.10.5 (transport in a type family is coercion along the action on paths of the type family).

transport-is-coe-of-ap : {A : 𝓤 ̇} {B : A → 𝓥 ̇} {x y : A} (p : x ≡ y) (u : B x) → transport B p u ≡ coe (ap B p) u
transport-is-coe-of-ap (refl x) u = refl _


-- Transport of functions along ua

transport-along-ua-is-pre-∘ : {A B : 𝓤 ̇} {C : 𝓥 ̇} (e : A ≃ B) (f : B → C) → transport (λ - → - → C) (ua A B e ⁻¹) f ≡ f ∘ (pr₁ e)
transport-along-ua-is-pre-∘ {𝓤} {𝓥} {A} {B} {C} e f = let p = ua A B e in
  funext _ _ (λ x → transport-fun' {A = id} {B = λ x → C} _ _ (p ⁻¹) f x ∙ transportconst C (p ⁻¹) _ ∙ ap f (ap (λ - → coe - x) (⁻¹-invol p) ∙ idtoeqv-β _ _ e x))

transport-along-ua-is-post-∘ : {A : 𝓤 ̇} {B C : 𝓥 ̇} (e : B ≃ C) (f : A → B) → transport (λ - → A → -) (ua B C e) f ≡ (pr₁ e) ∘ f
transport-along-ua-is-post-∘ {𝓤} {𝓥} {A} {B} {C} e f = let p = ua B C e in
  funext _ _ (λ x → transport-fun' {A = λ x → A} {B = id} _ _ p f x ∙ idtoeqv-β _ _ e _ ∙ ap (pr₁ e ∘ f) (transportconst A (p ⁻¹) x))




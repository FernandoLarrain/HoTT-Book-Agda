{-# OPTIONS --without-K --exact-split --safe #-}

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

idtoeqv : {A B : 𝓤 ̇} → (A ≡ B) → (A ≃ B)
idtoeqv {𝓤} {A} {B} p =
  coe p ,
  qinv-to-isequiv (ℍ A (λ B p → qinv (coe p)) (qinv-𝑖𝑑 A) B p)


-- Univalent universe

is-univalent : (𝓤 : Universe) → 𝓤 ⁺ ̇
is-univalent 𝓤 = {A B : 𝓤 ̇} → isequiv (idtoeqv {𝓤} {A} {B})

module is-univalent (isuniv : is-univalent 𝓤) {A B : 𝓤 ̇} where

  ua : A ≃ B → A ≡ B
  ua = qinv₁ (isequiv-to-qinv isuniv)

  idtoeqv-β' : idtoeqv ∘ ua ∼ 𝑖𝑑 (A ≃ B)
  idtoeqv-β' = qinv₂ (isequiv-to-qinv isuniv)

  idtoeqv-η : ua ∘ idtoeqv ∼ 𝑖𝑑 (A ≡ B)
  idtoeqv-η = qinv₃ (isequiv-to-qinv isuniv)


-- Axiom 2.10.3 (Univalence)

record Univalence : 𝓤ω where
  field
    ua : {𝓤 : Universe} {A B : 𝓤 ̇} → A ≃ B → A ≡ B
    idtoeqv-β' : {𝓤 : Universe} {A B : 𝓤 ̇} → idtoeqv ∘ ua ∼ 𝑖𝑑 (A ≃ B)
    idtoeqv-η : {𝓤 : Universe} {A B : 𝓤 ̇} → ua ∘ idtoeqv ∼ 𝑖𝑑 (A ≡ B)

open Univalence ⦃ ... ⦄ public


module _ ⦃ univ : Univalence ⦄ where

  -- Univalence axiom, as stated in the book.

  idtoeqv-is-equiv : {𝓤 : Universe} → is-univalent 𝓤
  idtoeqv-is-equiv = qinv-to-isequiv (ua , idtoeqv-β' , idtoeqv-η)
  
  -- Computation rule for univalence (underlying function)

  idtoeqv-β : {A B : 𝓤 ̇} → (f : A ≃ B) → coe (ua f) ∼ pr₁ f
  idtoeqv-β f = happly (pr₁ (dpr-≡ (idtoeqv-β' f)))


  -- Functoriality of ua  

  type-refl : (A : 𝓤 ̇) → refl A ≡ ua (≃-refl A)
  type-refl A = idtoeqv-η (refl A) ⁻¹ ∙ ap ua (refl _)

  type-sym : {A B : 𝓤 ̇} (f : A ≃ B) → ua f ⁻¹ ≡ ua (≃-sym f)
  type-sym {𝓤} {A} {B} f = lemma (ua f) ∙ ap (ua ∘ ≃-sym) (idtoeqv-β' f)
    where
    lemma : {A B : 𝓤 ̇} (p : A ≡ B) → p ⁻¹ ≡ ua (≃-sym (idtoeqv p))
    lemma (refl _) = type-refl _

  type-trans : {A B C : 𝓤 ̇} (e : A ≃ B) (f : B ≃ C) → ua e ∙ ua f ≡ ua (e ● f)
  type-trans {𝓤} {A} {B} {C} e f = lemma (ua e) (ua f) ∙ (ap (λ - →  ua (- ● idtoeqv (ua f))) (idtoeqv-β' e) ∙ ap (λ - → ua (e ● -)) (idtoeqv-β' f))
    where
    lemma : {A B C : 𝓤 ̇} (p : A ≡ B) (q : B ≡ C) → p ∙ q ≡ ua (idtoeqv p ● idtoeqv q)
    lemma (refl _) (refl _) = type-refl _


-- Lemma 2.10.5 (transport in a type family is coercion along the action on paths of the type family).

transport-is-coe-of-ap : {A : 𝓤 ̇} {B : A → 𝓥 ̇} {x y : A} (p : x ≡ y) (u : B x) → transport B p u ≡ coe (ap B p) u
transport-is-coe-of-ap (refl x) u = refl _


-- Transport of functions along ua

module _ ⦃ univ : Univalence ⦄ where

  transport-along-ua-is-pre-∘ : {A B : 𝓤 ̇} {C : 𝓥 ̇} (e : A ≃ B) (f : B → C) → transport (λ - → - → C) (ua e ⁻¹) f ∼ f ∘ pr₁ e
  transport-along-ua-is-pre-∘ {𝓤} {𝓥} {A} {B} {C} e f = let p = ua e in
    λ x → transport-fun (p ⁻¹) f x ∙ transportconst C (p ⁻¹) _ ∙ ap f (ap (λ - → coe - x) (⁻¹-invol p) ∙ idtoeqv-β e x)

  transport-along-ua-is-pre-∘' : {A B : 𝓤 ̇} {C : 𝓥 ̇} (e : A ≃ B) (f : A → C) → transport (λ - → - → C) (ua e) f ∼ f ∘ inv e
  transport-along-ua-is-pre-∘' {𝓤} {𝓥} {A} {B} {C} e f = let p = ua e in
    λ x → transport-fun p f x ∙ transportconst C p _ ∙ ap f (ap (λ - → coe - x) (type-sym e) ∙ idtoeqv-β (≃-sym e) x)

  transport-along-ua-is-post-∘ : {A : 𝓤 ̇} {B C : 𝓥 ̇} (e : B ≃ C) (f : A → B) → transport (λ - → A → -) (ua e) f ∼ pr₁ e ∘ f
  transport-along-ua-is-post-∘ {𝓤} {𝓥} {A} {B} {C} e f = let p = ua e in
    λ x → transport-fun p f x ∙ idtoeqv-β e _ ∙ ap (pr₁ e ∘ f) (transportconst A (p ⁻¹) x)

  transport-along-ua-is-post-∘' : {A : 𝓤 ̇} {B C : 𝓥 ̇} (e : B ≃ C) (f : A → C) → transport (λ - → A → -) (ua e ⁻¹) f ∼ inv e ∘ f
  transport-along-ua-is-post-∘' {𝓤} {𝓥} {A} {B} {C} e f = let p = ua e in
    λ x → transport-fun (p ⁻¹) f x ∙ (ap (λ - → coe - (f (transport (λ x → A) ((p ⁻¹) ⁻¹) x))) (type-sym e) ∙ idtoeqv-β (≃-sym e) _ ∙ ap (inv e ∘ f) (transportconst A ((p ⁻¹) ⁻¹) x))

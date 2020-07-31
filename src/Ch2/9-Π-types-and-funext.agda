{-# OPTIONS --without-K --exact-split #-}

open import Ch1.Type-theory
open import Ch2.1-Types-are-higher-groupoids
open import Ch2.2-Functions-are-functors
open import Ch2.3-Type-families-are-fibrations
open import Ch2.4-Homotopies-and-equivalences
open import Ch2.7-Σ-types

module Ch2.9-Π-types-and-funext where


-- Function extensionality.

-- (i) From equality to homotopy

happly : {A : 𝓤 ̇ } {B : A → 𝓥 ̇ } {f g : Π B} → f ≡ g → f ∼ g
happly (refl f) x = refl (f x)

-- (ii) Axiom 2.9.3 (Function extensionality).

-- (ii).1 Definition of function extensionality for a pair of universes

has-funext : (𝓤 𝓥 : Universe) → (𝓤 ⊔ 𝓥) ⁺ ̇
has-funext 𝓤 𝓥 = {A : 𝓤 ̇ } {B : A → 𝓥 ̇ } {f g : Π B} → isequiv (happly {𝓤} {𝓥} {A} {B} {f} {g})

-- (ii).2 Definition of global function extensionality

Function-Extensionality : 𝓤ω
Function-Extensionality = {𝓤 𝓥 : Universe} → has-funext 𝓤 𝓥

-- (ii).3 Postulating the axiom

postulate
  fe : Function-Extensionality


-- (iii) From homotopy to equality

funext : {A : 𝓤 ̇ } {B : A → 𝓥 ̇ } {f g : Π B} → (f ∼ g) → (f ≡ g)
funext = qinv₁ (isequiv-to-qinv fe)


-- (iv) Computation rules for function extensionality

happly-β : {A : 𝓤 ̇ } {B : A → 𝓥 ̇ } {f g : Π B} (h : f ∼ g) → happly (funext h) ∼ h
happly-β h = happly (qinv₂ (isequiv-to-qinv fe) h)


-- (v) Uniqueness rules for function extensionality

happly-η : {A : 𝓤 ̇ } {B : A → 𝓥 ̇ } {f g : Π B} (p : f ≡ g) → funext (happly p) ≡ p
happly-η = qinv₃ (isequiv-to-qinv fe)


-- Pointwise characterization of refl, _⁻¹ and _∙_.

fun-refl : {A : 𝓤 ̇ } {B : A → 𝓥 ̇ } (f : Π B) → refl f ≡ funext (λ x → refl (f x))
fun-refl f = (happly-η (refl f)) ⁻¹

fun-sym : {A : 𝓤 ̇ } {B : A → 𝓥 ̇ } {f g : Π B} (α : f ≡ g) → (α ⁻¹) ≡ funext (λ x → (happly α x) ⁻¹)
fun-sym (refl f) = fun-refl f

fun-trans : {A : 𝓤 ̇ } {B : A → 𝓥 ̇ } {f g h : Π B} (α : f ≡ g) (β : g ≡ h) → (α ∙ β) ≡ funext (λ x → happly α x ∙ happly β x)
fun-trans (refl f) (refl f) = fun-refl f


-- Equation 2.9.4 (Transport of functions).

transport-fun : {X : 𝓤 ̇} {A : X → 𝓥 ̇} {B : X → 𝓦 ̇} {x₁ x₂ : X} (p : x₁ ≡ x₂) (f : A x₁ → B x₁) → transport (λ - → A - → B -) p f ∼ transport B p ∘ f ∘ transport A (p ⁻¹)
transport-fun (refl _) f a = refl (f a)


-- Equation 2.9.5 (Transport of dependent functions).

transport-dfun : {X : 𝓤 ̇} {A : X → 𝓥 ̇ } {B : (x : X) → A x → 𝓥 ̇ } {x₁ x₂ : X} (p : x₁ ≡ x₂) (f : (a : A x₁) → B x₁ a) → (a : A x₁) → transport (λ - → (a : A -) → B - a) p f (transport A p a) ≡ transport (λ - → (Σ-induction B) -) (dpair-≡ (p , refl (transport A p a))) (f a)
transport-dfun (refl _) f a = refl (f a)


-- Lemma 2.9.6 (Function extensionality with respect to dependent paths; equality of parameterized functions).

module dpath-funext {X : 𝓤 ̇} (A B : X → 𝓥 ̇) where

  P : X → 𝓥 ̇
  P x = A x → B x

  equiv :{x y : X} (p : x ≡ y) (f : P x) (g : P y) → (transport P p f ≡ g) ≃ ((a : A x) → transport B p (f a) ≡ g (transport A p a))
  equiv (refl _) f g = happly , fe 

  module paths {x y : X} (p : x ≡ y) (f : P x) (g : P y) (q : transport P p f ≡ g) (a : A x) where

    i : transport P p f (transport A p a) ≡ transport B p (f (transport A (p ⁻¹) (transport A p a)))
    i = transport-fun p f (transport A p a)

    j : transport B p (f (transport A (p ⁻¹) (transport A p a))) ≡ transport B p (f a)
    j = ap (transport B p ∘ f) (transport-∙ A p (p ⁻¹) a ∙ happly (ap (transport A) (rinv p)) a)
    
    k : transport B p (f a) ≡ g (transport A p a) 
    k = pr₁ (equiv p f g) q a

    ijk = i ∙ j ∙ k

  open paths

  path-≡ : {x y : X} (p : x ≡ y) (f : P x) (g : P y) (q : transport P p f ≡ g) (a : A x) → happly q (transport A p a) ≡ ijk p f g q a
  path-≡ (refl x) f g q a = lu _


-- Lemma 2.9.7

module dpath-dfunext {X : 𝓤 ̇} (A : X → 𝓥 ̇) (B : (x : X) → A x → 𝓥 ̇) where

  P : X → 𝓥 ̇
  P x = (a : A x) → B x a

  equiv : {x y : X} (p : x ≡ y) (f : P x) (g : P y) → (transport P p f ≡ g) ≃ ((a : A x) → transport (Σ-induction B) (dpair-≡ (p , refl (transport A p a))) (f a) ≡ g (transport A p a))
  equiv (refl _) f g = happly , fe

  -- TO DO: computation rule.

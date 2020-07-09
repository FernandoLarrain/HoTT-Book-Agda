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

happly : {A : 𝓤 ̇ } {B : A → 𝓥 ̇ } (f g : Π B) → f ≡ g → f ∼ g
happly f f (refl f) x = refl (f x)


-- (ii) Axiom 2.9.3 (Function extensionality).

-- (ii).1 Definition of function extensionality for a pair of universes

hfunext : ∀ 𝓤 𝓥 → (𝓤 ⊔ 𝓥)⁺ ̇
hfunext 𝓤 𝓥 = {A : 𝓤 ̇ } {B : A → 𝓥 ̇ } (f g : Π B) → isequiv (happly f g)

-- (ii).2 Definition of global function extensionality

global-hfunext : 𝓤ω
global-hfunext = ∀ {𝓤 𝓥} → hfunext 𝓤 𝓥

-- (ii).3 Postulating the axiom

postulate
  hfe : global-hfunext

-- (iii) From homotopy to equality

funext : {A : 𝓤 ̇ } {B : A → 𝓥 ̇ } (f g : Π B) → (f ∼ g) → (f ≡ g)
funext f g = qinv₁ (isequiv-to-qinv (hfe f g))


-- (iv) Computation rules for function extensionality

happly-β : {A : 𝓤 ̇ } {B : A → 𝓥 ̇ } (f g : Π B) (h : f ∼ g) → happly f g (funext f g h) ∼ h
happly-β f g h = happly _ _ (qinv₂ (isequiv-to-qinv (hfe f g)) h)

happly-β' : {A : 𝓤 ̇ } {B : A → 𝓥 ̇ } (f g : Π B) (h : f ∼ g) → happly f g (funext f g h) ≡ h
happly-β' f g h = funext _ _ (happly-β f g h)

happly-β'' : {A : 𝓤 ̇ } {B : A → 𝓥 ̇ } (f g : Π B) → (happly f g ∘ funext f g) ≡ id
happly-β'' f g = funext _ _ (λ h → funext _ _ (happly-β f g h))


-- (v) Uniqueness rules for function extensionality

happly-η : {A : 𝓤 ̇ } {B : A → 𝓥 ̇ } (f g : Π B) (p : f ≡ g) → funext f g (happly f g p) ≡ p
happly-η f g = qinv₃ (isequiv-to-qinv (hfe f g))

happly-η' : {A : 𝓤 ̇ } {B : A → 𝓥 ̇ } (f g : Π B) → (funext f g ∘ happly f g) ≡ id
happly-η' f g = funext _ _ (happly-η f g)


-- Pointwise characterization of refl, _⁻¹ and _∙_.

fun-refl : {A : 𝓤 ̇ } {B : A → 𝓥 ̇ } (f : Π B) → refl f ≡ funext f f (λ x → refl (f x))
fun-refl f = (happly-η _ _ (refl f)) ⁻¹

fun-sym : {A : 𝓤 ̇ } {B : A → 𝓥 ̇ } (f g : Π B) (α : f ≡ g) → (α ⁻¹) ≡ funext g f (λ x → (happly f g α x) ⁻¹)
fun-sym f f (refl f) = fun-refl f

fun-trans : {A : 𝓤 ̇ } {B : A → 𝓥 ̇ } (f g h : Π B) (α : f ≡ g) (β : g ≡ h) → (α ∙ β) ≡ funext f h (λ x → happly f g α x ∙ happly g h β x)
fun-trans f .f .f (refl .f) (refl .f) = fun-refl f
  

-- Equation 2.9.4 (Transport of functions).

-- (i) Commutative square version

transport-fun : {X : 𝓤 ̇} {A : X → 𝓥 ̇} {B : X → 𝓦 ̇} (x₁ x₂ : X) (p : x₁ ≡ x₂) (f : A x₁ → B x₁) → transport (λ - → A - → B -) p f ∘ transport A p ∼ transport B p ∘ f
transport-fun x₁ .x₁ (refl .x₁) f a = refl (f a)

-- (ii) Book version

transport-fun' : {X : 𝓤 ̇} {A : X → 𝓥 ̇} {B : X → 𝓦 ̇} (x₁ x₂ : X) (p : x₁ ≡ x₂) (f : A x₁ → B x₁) → transport (λ - → A - → B -) p f ∼ transport B p ∘ f ∘ transport A (p ⁻¹)
transport-fun' x₁ .x₁ (refl .x₁) f a = refl (f a)


-- Equation 2.9.5 (Transport of dependent functions).

transport-dfun : {X : 𝓤 ̇} {A : X → 𝓥 ̇ } {B : (x : X) → A x → 𝓥 ̇ } (x₁ x₂ : X) (p : x₁ ≡ x₂) (f : (a : A x₁) → B x₁ a) → (a : A x₁) → transport (λ - → (a : A -) → B - a) p f (transport A p a) ≡ transport (λ - → (λ z → B (pr₁ z) (pr₂ z)) -) (dpair-≡ (p , refl (transport A p a))) (f a)
transport-dfun x₁ .x₁ (refl .x₁) f a = refl (f a)


-- Lemma 2.9.6 (Function extensionality with respect to dependent paths; equality of parameterized functions).

module dfunext {X : 𝓤 ̇} (A B : X → 𝓥 ̇) where

  P : X → 𝓥 ̇
  P x = A x → B x

  equiv : (x y : X) (p : x ≡ y) (f : A x → B x) (g : A y → B y) → (transport P p f ≡ g) ≃ ((a : A x) → transport B p (f a) ≡ g (transport A p a))
  equiv x .x (refl .x) f g = (happly f g) , (hfe f g)

  module paths {x y : X} (p : x ≡ y) (f : A x → B x) (g : A y → B y) (q : transport P p f ≡ g) (a : A x) where

    i : transport P p f (transport A p a) ≡ transport B p (f (transport A (p ⁻¹) (transport A p a)))
    i = transport-fun' x y p f (transport A p a)

    j : transport B p (f (transport A (p ⁻¹) (transport A p a))) ≡ transport B p (f a)
    j = ap (transport B p ∘ f) (transport-∙ A p (p ⁻¹) a ∙ happly (transport A(p ∙ p ⁻¹)) (𝑖𝑑 (A x)) (ap (transport A) (rinv p)) a)
    
    k : transport B p (f a) ≡ g (transport A p a) 
    k = pr₁ (equiv x y p f g) q a

    ijk = i ∙ j ∙ k

  open paths

  path-≡ : (x y : X) (p : x ≡ y) (f : A x → B x) (g : A y → B y) (q : transport P p f ≡ g) (a : A x) → happly (transport P p f) g q (transport A p a) ≡ ijk p f g q a
  path-≡ x .x (refl .x) f g q a = lu _


-- Lemma 2.9.7 [TO DO]

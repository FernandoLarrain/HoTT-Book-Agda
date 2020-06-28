{-# OPTIONS --without-K --exact-split #-}

open import Ch1.Type-theory
open import Ch2.1-Types-are-higher-groupoids
open import Ch2.2-Functions-are-functors
open import Ch2.3-Type-families-are-fibrations
open import Ch2.4-Homotopies-and-equivalences
open import Ch2.6-Cartesian-product-types
open import Ch2.7-Σ-types
open import Ch2.9-Π-types-and-funext
open import Ch2.10-Universes-and-univalence

module Ch2.14-Equality-of-structures where


-- Definition 2.14.1 (Semigroup)

Assoc : (Σ A ꞉ 𝓤 ̇ , (A → A → A)) → 𝓤 ̇
Assoc (A , m) =  (x y z : A) → m x (m y z) ≡ m (m x y) z

SemigroupStr : (A : 𝓤 ̇) → 𝓤 ̇
SemigroupStr A = Σ m ꞉ (A → A → A) , Assoc (A , m)

Semigroup : (𝓤 : Universe) → 𝓤 ⁺ ̇
Semigroup 𝓤 = Σ A ꞉ 𝓤 ̇ , SemigroupStr A


-- Subsection 2.14.1: Lifting equivalences.

module Lifting-equivalences (A B : 𝓤 ̇) (e : A ≃ B) (m : A → A → A) (a : Assoc (A , m)) where

  -- Naming equivalence data
  
  f : A → B
  f = pr₁ e
  
  i : isequiv f
  i = pr₂ e

  q : qinv f
  q = isequiv-to-qinv i

  f⁻¹ : B → A
  f⁻¹ = qinv₁ q

  α : f ∘ f⁻¹ ∼ id
  α = qinv₂ q

  β : f⁻¹ ∘ f ∼ id
  β = qinv₃ q
  
  p : A ≡ B
  p = ua A B e

  -- Semigroup structure on A induces a semigroup structure on B

  induced-sgrp-str : SemigroupStr A → SemigroupStr B
  induced-sgrp-str = transport SemigroupStr p

  -- The previous structure-inducing map is an equivalence

  sgrp-str-≃ : SemigroupStr A ≃ SemigroupStr B
  sgrp-str-≃ = transport SemigroupStr p , qinv-to-isequiv (qinv-transport SemigroupStr p)


  -- Characterization of induced structure

  -- (i) Induced operation

  m' : B → B → B
  m' = transport (λ X → X → X → X) p m

  -- (ii) Induced associator
  
  a' : Assoc (B , m')
  a' = transport Assoc (dpair-≡ (p , refl m')) a

  -- (iii) Proof
  
  sgrp-str-characterization : transport SemigroupStr p (m , a) ≡ (m' , a')
  sgrp-str-characterization = transport-dpair {A = 𝓤 ̇} {P = λ X → X → X → X} {Q = Assoc} p m a

  m'-characterization : m' ≡ (λ b₁ b₂ → f (m (f⁻¹ b₁) (f⁻¹ b₂)))
  m'-characterization = funext _ _ λ b₁ → transport-fun' {X = 𝓤 ̇} {A = id} {B = λ X → X → X} _ _ p m b₁ ∙ funext _ _ λ b₂ → transport-fun' {X = 𝓤 ̇} {A = id} {B = id} _ _ p _ _ ∙ (happly _ _ aux _ ∙ ap f ( ap (m (transport id (ua A B e ⁻¹) b₁)) (happly _ _ aux⁻¹ _) ∙ ap (λ - → m - (f⁻¹ b₂)) (happly _ _ aux⁻¹ _) )) where
    aux : transport id (ua A B e) ≡ f
    aux = funext _ _ (idtoeqv-β A B e)
    aux⁻¹ : transport id (ua A B e ⁻¹) ≡ f⁻¹
    aux⁻¹ = ap (transport id) (type-sym _ _ e) ∙ funext _ _ (idtoeqv-β _ _ (≃-sym e))

  associativity-eqn : Assoc (B , m')
  associativity-eqn b₁ b₂ b₃ = happly _ _ (happly _ _ m'-characterization b₁) (m' b₂ b₃) ∙
    ap (λ - → f (m (f⁻¹ b₁) (f⁻¹ -))) (happly _ _ (happly _ _ m'-characterization b₂) b₃) ∙
    ap (λ - → f ( m (f⁻¹ b₁) -)) (β (m (f⁻¹ b₂) (f⁻¹ b₃))) ∙
    ap f (a _ _ _) ∙
    ap (λ - → f (m - (f⁻¹ b₃))) (β (m (f⁻¹ b₁) (f⁻¹ b₂)) ⁻¹) ∙
    ap (λ - → f (m (f⁻¹ -) (f⁻¹ b₃))) (happly _ _ (happly _ _ (m'-characterization ⁻¹)  b₁) b₂) ∙
    happly _ _ (happly _ _ (m'-characterization ⁻¹) (m' b₁ b₂)) b₃

  -- TO DO

  -- a'-characterization : a' ≡ associativity-eqn
  -- a'-characterization = funext _ _ (λ b₁ → funext _ _ (λ b₂ → funext _ _ (λ b₃ → {!!})))


-- Subsection 2.14.2: Equality of semigroups.

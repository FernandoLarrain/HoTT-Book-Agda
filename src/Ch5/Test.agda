{-# OPTIONS --without-K --exact-split #-}

module Ch5.Test where

open import Agda.Primitive public


-- I. Necessary Definitions

-- (i) Sigma types

record Σ {i j} (X : Set i) (Y : X → Set j) : Set (i ⊔ j) where
  constructor
    _,_
  field
    fst : X
    snd : Y fst

open Σ public

-- (ii) Identity types

data Id {i} (X : Set i) : X → X → Set i where
 refl : (x : X) → Id X x x

infix 0 Id

{-# BUILTIN EQUALITY Id #-}

_≡_ : {i : Level} {X : Set i} → X → X → Set i
x ≡ y = Id _ x y

infix 0 _≡_

-- (iii) Basic operations

ap : {i j : Level} {X : Set i} {Y : Set j} (f : X → Y) {x y : X} → x ≡ y → f x ≡ f y
ap f (refl x) = refl (f x)

_∙_ : {i : Level} {X : Set i} {x y z : X} → x ≡ y → y ≡ z → x ≡ z
refl x ∙ refl x = refl x

_∘_ : {i j k : Level} {A : Set i} {B : Set j} {C : Set k} → (B → C) → (A → B) → (A → C)
g ∘ f = λ a → g (f a)


-- II. The Problem

variable
  i : Level

-- Algebras

Alg : (i : Level) → Set (lsuc i)
Alg i = Σ (Set i) (λ A → A → A)

-- Homomorphisms (using Σ)

Hom : Alg i → Alg i → Set i
Hom (A , s) (B , t) = Σ (A → B) (λ f → (a : A) → f (s a) ≡ t (f a))

-- Homomorphism composition (using Σ)

_○_ : {A B C : Alg i} → Hom B C → Hom A B → Hom A C
(g , β) ○ (f , α) = (g ∘ f) , (λ c → ap g (α c) ∙ β (f c))

module _ (A B : Alg i) (f : Hom A B) (g : Hom B A) (h : Hom A A) where

  _ : g ○ f ≡ h -- Error. Can see where the problem might be by normalizing g ○ f: g does not appear in the expression, but f does.
  _ = {!!}

  _ : _○_ {C = A} g f ≡ h -- No error. But then, why do records work without this info? See below.
  _ = {!!}

-- Homomorphisms (using records)

record Hom' (A B : Alg i) : Set i where
  field
    fun : A .fst → B .fst
    comm : (a : A .fst) → fun (A .snd a) ≡ B .snd (fun a)

-- Homomorphism composition (using records)

_◎_ : {A B C : Alg i} → Hom' B C → Hom' A B → Hom' A C
record { fun = g ; comm = β } ◎ record { fun = f ; comm = α } = record { fun = g ∘ f ; comm = λ c → ap g (α c) ∙ β (f c) }

module _ (A B : Alg i) (f : Hom' A B) (g : Hom' B A) (h : Hom' A A) where

  _ : g ◎ f ≡ h -- No error, even though no info other than g and f is provided.
  _ = {!!}

record T (A : Set i) : Set i where
  field
    left : A
    right : A




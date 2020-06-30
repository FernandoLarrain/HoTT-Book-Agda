{-# OPTIONS --without-K --exact-split --rewriting #-}

open import Ch1.Type-theory
open import Ch2.Homotopy-type-theory
open import Ch3.Sets-and-logic
open import Ch6.2-Induction-pples-and-dependent-paths

module Ch6.4-Circles-and-spheres where


-- Lemma 6.4.1 (The circle is non-trivial).

𝕊¹-is-non-trivial : ¬ (loop ≡ refl base¹)
𝕊¹-is-non-trivial s = 𝓤₀-is-not-set λ x y p q → ∙ₗ-inv (q ⁻¹) p q (loop-β' y (q ⁻¹ ∙ p) ⁻¹ ∙ ap (ap (𝕊¹-rec y (q ⁻¹ ∙ p))) s ∙ (linv q ⁻¹))


-- Lemma 6.4.2 TO DO


-- Lemma 6.4.3 TO DO


-- Lemma 6.4.4 (Action on 2-paths).

module _ {A : 𝓤 ̇ } {B : 𝓥 ̇ } (f : A → B) where

  ap² :  {x y : A} {p q : x ≡ y} → p ≡ q → ap f p ≡ ap f q
  ap² (refl p) = refl (ap f p)

  -- Remark (relationship between ap² and ap).

  ap²-is-ap-of-ap : {x y : A} {p q : x ≡ y} → (r : p ≡ q) → ap² r ≡ ap (ap f) r
  ap²-is-ap-of-ap (refl r) = refl _

  -- Alternative definition of ap².

  ap²' : {x y : A} {p q : x ≡ y} → p ≡ q → ap f p ≡ ap f q
  ap²' = ap (ap f)


-- Lemma 6.4.5 (Two-dimensional transport).

module _ {A : 𝓤 ̇ } (P : A → 𝓥 ̇) where

  transport² :  {x y : A} {p q : x ≡ y} → p ≡ q → (u : P x) → transport P p u ≡ transport P q u
  transport² (refl p) u = refl (transport P p u)

  -- Remark (relationship between transport² and transport).

  transport²-is-transport-along-transport : {x y : A} {p q : x ≡ y} (r : p ≡ q) (u : P x) → transport² r u ≡ transport (λ (- : x ≡ y) → transport P p u ≡ transport P - u) r (refl (transport P p u))
  transport²-is-transport-along-transport (refl p) u = refl (refl (transport P p u))

  -- Alternative definition of transport².

  transport²' : {x y : A} {p q : x ≡ y} → p ≡ q → (u : P x) → transport P p u ≡ transport P q u
  transport²' {x} {y} {p} r u = transport (λ (q : x ≡ y) → transport P p u ≡ transport P q u) r (refl (transport P p u))


-- Lemma (transport² and transport²' in constant family).

transport²const : {A : 𝓤 ̇} (B : 𝓥 ̇) {x y : A} {p q : x ≡ y} (r : p ≡ q) (b : B) → transport² (λ a → B) r b ≡ transportconst B p b ∙ transportconst B q b ⁻¹
transport²const B (refl (refl x)) b = refl _

transport²'const : {A : 𝓤 ̇} (B : 𝓥 ̇) {x y : A} {p q : x ≡ y} (r : p ≡ q) (b : B) → transport²' (λ a → B) r b ≡ transportconst B p b ∙ transportconst B q b ⁻¹
transport²'const B (refl (refl x)) b = refl _


-- Definition of the type of dependent 2-paths.

PathOver² : {A : 𝓤 ̇} (P : A → 𝓥 ̇) {x y : A} {p q : x ≡ y} (r : p ≡ q) {u : P x} {v : P y} (h : u ≡ v [ P ↓ p ]) (k : u ≡ v [ P ↓ q ]) → 𝓥 ̇
PathOver² P r {u} h k = h ≡ transport² P r u ∙ k

infix 0 PathOver²

syntax PathOver² P r h k = h ≡ k [ P ⇊ r ]

-- Remark (relationship between PathOver² and PathOver).

PathOver²-≡-PathOver-PathOver : {A : 𝓤 ̇} (P : A → 𝓥 ̇) {x y : A} {p q : x ≡ y} (r : p ≡ q) {u : P x} {v : P y} (h : u ≡ v [ P ↓ p ]) (k : u ≡ v [ P ↓ q ]) → (h ≡ k [ P ⇊ r ]) ≡ (h ≡ k [ (λ (- : x ≡ y) → u ≡ v [ P ↓ - ]) ↓ r ])
PathOver²-≡-PathOver-PathOver P {x} {.x} {.(refl x)} {.(refl x)} (refl (refl x)) h (refl u) = refl _


-- Lemma 6.4.6 (Dependent action on 2-paths).

module _ {A : 𝓤 ̇} {P : A → 𝓥 ̇} {x y : A} {p q : x ≡ y} (f : (x : A) → P x) where
  apd² : (r : p ≡ q) → apd f p ≡ apd f q [ P ⇊ r ]
  apd² (refl p) = lu _

  -- Alernative definition of dependent action on 2-paths.

  apd²' : (r : p ≡ q) → apd f p ≡ apd f q [ (λ - → f x ≡ f y [ P ↓ - ]) ↓ r ]
  apd²' (refl p) = refl (apd f p) 


-- Lemma (apd² and apd²' reduce to ap² when family is constant).

apd²-const : {A : 𝓤 ̇} (B : 𝓥 ̇) {x y : A} {p q : x ≡ y} (f : A → B) (r : p ≡ q) → apd² f r ≡ apd-const B f p ∙ (transportconst B p (f x) ∙ₗ (ap² f r ∙ apd-const' B f q)) ∙ ∙-assoc _ _ _ ∙ (transport²const B r (f x) ⁻¹ ∙ᵣ apd f q)
apd²-const B {x} {.x} {.(refl x)} {.(refl x)} f (refl (refl x)) = refl _


{- Note: There's a slight inconsistency in the book. Let f = 𝕊²-ind. Then, 
  
  apd² f surf : adp f (refl base²) ≡ apd f (refl base²) [ P ⇊ surf ] , 

while 
  
  s : refl b ≡ refl b [ (λ p → b ≡ b [ P ↓ p ] ↓ surf ] .

As shown above, these two types are equal, but not judgmentally. We opted for PathOver². -}


-- The Sphere, 𝕊².

postulate

  -- (i) Type formation rule

  𝕊² : 𝓤₀ ̇

  -- (ii) Constructors
  
  base² : 𝕊²
  surf : refl base² ≡ refl base²

module _ (P : 𝕊² → 𝓤 ̇) (b : P base²) (s : refl b ≡ refl b [ P ⇊ surf ]) where

  postulate

    -- (iii) Induction principle

    𝕊²-ind : Π P
  
    -- (iv) Computation rules

    base²-β : 𝕊²-ind base² ↦ b

    {-# REWRITE base²-β #-}

    surf-β : apd² 𝕊²-ind surf ≡ s


-- Recursion principle for 𝕊²

module _ {B : 𝓤 ̇} (b : B) (s : refl b ≡ refl b) where

  𝕊²-rec : 𝕊² → B
  𝕊²-rec = 𝕊²-ind (λ x → B) b (s ∙ (transport²const B surf b ⁻¹ ∙ ru _))

  base²-β' : 𝕊²-rec base² ≡ b
  base²-β' = refl _

  surf-β' : ap² 𝕊²-rec surf ≡ s
  surf-β' =  ru _ ∙ lu _ ∙ ru _ ∙ lu _ ∙ ru _ ∙ ∙ᵣ-inv _ _ _ (ap (λ - → refl (refl (𝕊²-rec base²)) ∙ (refl (refl (𝕊²-rec base²)) ∙ (ap² 𝕊²-rec surf ∙ refl (refl (𝕊²-rec base²))) ∙ refl (refl (𝕊²-rec base²))) ∙ refl (refl (𝕊²-rec base²)) ∙ (- ∙ ru (transport² (λ a → B) surf (𝕊²-rec base²)))) (lu (transport²const B surf (𝕊²-rec base²) ⁻¹)) ∙ (apd²-const B 𝕊²-rec surf ⁻¹ ∙ surf-β (λ x → B) b (s ∙ (transport²const B surf b ⁻¹ ∙ ru _))))


-- TO DO: Improve readability of previous proof!

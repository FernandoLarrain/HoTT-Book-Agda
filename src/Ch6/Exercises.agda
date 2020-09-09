{-# OPTIONS --without-K --exact-split --safe #-}

open import Ch1.Type-theory
open import Ch2.Homotopy-type-theory
open import Ch3.Sets-and-logic
open import Ch4.Equivalences
open import Ch6.4-Circles-and-spheres-safe

module Ch6.Exercises where

-- Exercise 2.4 continued.

module exercise-2-4-continued where


  -- PathOver

  module PathOver'-1-is-PathOver ⦃ univ : Univalence ⦄ where

    open higher-paths

    BndryOver-agreement : {X : 𝓤 ̇} (P : X → 𝓥 ̇) (b : Bndry 1 X) → BndryOver 1 P b ≡ P (lhs b) × P (rhs b)
    BndryOver-agreement P b = ua (pr₂ , qinv-to-isequiv ((lift ⋆ ,_) , (refl , β)))
      where
      β :  (lift ⋆ ,_) ∘ pr₂ ∼ id
      β (lift ⋆ , w) = dpair-≡ ((refl _) , (refl _))

    BndryOver-agreement' : {X : 𝓤 ̇} (P : X → 𝓥 ̇) (b : Bndry 1 X) → BndryOver 1 P b ≃ P (lhs b) × P (rhs b)
    BndryOver-agreement' P b = (pr₂ , qinv-to-isequiv ((lift ⋆ ,_) , (refl , β)))
      where
      β :  (lift ⋆ ,_) ∘ pr₂ ∼ id
      β (lift ⋆ , w) = dpair-≡ ((refl _) , (refl _))

    {- Alternatively, use Σ-over-Contr-base-is-fib -}

    PathOver-agreement : {X : 𝓤 ̇} (P : X → 𝓥 ̇) {b : Bndry 1 X} (p : Path 1 b) (b' : BndryOver 1 P b) → PathOver' 1 P {b} p b' ≡ PathOver P p (pr₁ (pr₂ b')) (pr₂ (pr₂ b')) 
    PathOver-agreement P (refl _) b' = refl _

    PathOver-agreement' : {X : 𝓤 ̇} (P : X → 𝓥 ̇) {b : Bndry 1 X} (p : Path 1 b) (b' : BndryOver 1 P b) → PathOver' 1 P {b} p b' ≃ PathOver P p (pr₁ (pr₂ b')) (pr₂ (pr₂ b')) 
    PathOver-agreement' P p b' = idtoeqv (PathOver-agreement P p b')


  -- Lemma 6.4.4 (Action on 2-paths).

  module _ {A : 𝓤 ̇ } {B : 𝓥 ̇ } (f : A → B) where

    -- Remark (relationship between ap² and ap).

    ap²-is-ap-of-ap : {x y : A} {p q : x ≡ y} → (r : p ≡ q) → ap² f r ≡ ap (ap f) r
    ap²-is-ap-of-ap (refl r) = refl _

    -- Alternative definition of ap².

    ap²' : {x y : A} {p q : x ≡ y} → p ≡ q → ap f p ≡ ap f q
    ap²' = ap (ap f)

    module ap'-2-is-ap² where

      open higher-paths

      private

        type-agreement : (b : Bndry 2 A) (r : Path 2 b) → ap'Codom 2 f b r ≡ type-of (ap² f r)
        type-agreement ((b , x , .x) , refl .x , .(refl x)) (refl .(refl x)) = refl _

        term-agreement : (b : Bndry 2 A) (r : Path 2 b) → coe (type-agreement b r) (ap' 2 f r) ≡ ap² f r  
        term-agreement ((b , x , .x) , refl .x , .(refl x)) (refl .(refl x)) = refl _


  -- Lemma 6.4.5 (Two-dimensional transport).

  module _ {A : 𝓤 ̇ } (P : A → 𝓥 ̇) where

    -- Remark (relationship between transport² and transport).

    transport²-is-transport-along-transport : {x y : A} {p q : x ≡ y} (r : p ≡ q) (u : P x) → transport² P r u ≡ transport (λ (- : x ≡ y) → transport P p u ≡ transport P - u) r (refl (transport P p u))
    transport²-is-transport-along-transport (refl p) u = refl (refl (transport P p u))

    -- Alternative definition of transport².

    transport²' : {x y : A} {p q : x ≡ y} → p ≡ q → (u : P x) → transport P p u ≡ transport P q u
    transport²' {x} {y} {p} r u = transport (λ (q : x ≡ y) → transport P p u ≡ transport P q u) r (refl (transport P p u))

    module transport'-1-is-transport² where

      open higher-paths

      private

        type-agreement : (b : Bndry 2 A) (r : Path 2 b) (u : P (left-basept b)) → transport'Codom 1 P b r u ≡ type-of (transport² P r u)
        type-agreement ((b , x , .x) , refl .x , .(refl x)) (refl .(refl x)) u = refl _

        term-agreement : (b : Bndry 2 A) (r : Path 2 b) (u : P (left-basept b)) → coe (type-agreement b r u) (transport' 1 P r u) ≡ transport² P r u 
        term-agreement ((b , x , .x) , refl .x , .(refl x)) (refl .(refl x)) u = refl _


  -- Lemma (transport²' in constant family).

  transport²'const : {A : 𝓤 ̇} (B : 𝓥 ̇) {x y : A} {p q : x ≡ y} (r : p ≡ q) (b : B) → transport²' (λ a → B) r b ≡ transportconst B p b ∙ transportconst B q b ⁻¹
  transport²'const B (refl (refl x)) b = refl _


  -- Remark (relationship between PathOver² and PathOver).

  PathOver²-≡-PathOver-PathOver : {A : 𝓤 ̇} (P : A → 𝓥 ̇) {x y : A} {p q : x ≡ y} (r : p ≡ q) {u : P x} {v : P y} (h : u ≡ v [ P ↓ p ]) (k : u ≡ v [ P ↓ q ]) → (h ≡ k [ P ⇊ r ]) ≡ (h ≡ k [ (λ (- : x ≡ y) → u ≡ v [ P ↓ - ]) ↓ r ])
  PathOver²-≡-PathOver-PathOver P {x} {.x} {.(refl x)} {.(refl x)} (refl (refl x)) h (refl u) = refl _

  module PathOver'-2-is-PathOver² ⦃ univ : Univalence ⦄ where

    open higher-paths
    open PathOver'-1-is-PathOver

    private

      BndryOver²-agreement : {X : 𝓤 ̇} (P : X → 𝓥 ̇) (b : Bndry 2 X) → BndryOver 2 P b ≃ -Σ (P (lhs (pr₁ b)) × P (rhs (pr₁ b))) (Σ-induction λ u v → PathOver P (lhs b) u v × PathOver P (rhs b) u v)
      BndryOver²-agreement {𝓤} {𝓥} P ((lift ⋆ , x , y) , p , q) = Σ-preserves-≃ _ _ base-≃ (Σ-induction (Lift-induction _ _ _ (𝟙-induction _ (Σ-induction (λ u v → ×-preserves-≃ (PathOver-agreement' P p _) (PathOver-agreement' P q _))))))
        where
        base-≃ : BndryOver 1 P (lift ⋆ , x , y) ≃ P x × P y
        base-≃ = BndryOver-agreement' P (lift ⋆ , x , y)


  -- Lemma 6.4.6 (Dependent action on 2-paths).

  module _ {A : 𝓤 ̇} {P : A → 𝓥 ̇} {x y : A} {p q : x ≡ y} (f : (x : A) → P x) where

    -- Alternative definition of dependent action on 2-paths.

    apd²' : (r : p ≡ q) → apd f p ≡ apd f q [ (λ - → f x ≡ f y [ P ↓ - ]) ↓ r ]
    apd²' (refl p) = refl (apd f p) 

  module apd'-2-is-apd² {A : 𝓤 ̇} {P : A → 𝓥 ̇} (f : (x : A) → P x) where

    open higher-paths

    private

      type-agreement : (b : Bndry 2 A) (r : Path 2 b) → apd'Codom 2 f b r ≡ type-of (apd² f r)
      type-agreement ((b , x , .x) , refl .x , .(refl x)) (refl .(refl x)) = refl _

      term-agreement : (b : Bndry 2 A) (r : Path 2 b) → coe (type-agreement b r) (apd' 2 f r) ≡ apd² f r  
      term-agreement ((b , x , .x) , refl .x , .(refl x)) (refl .(refl x)) = refl _

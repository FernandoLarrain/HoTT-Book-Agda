{-# OPTIONS --without-K --exact-split #-}

open import Ch1.Type-theory
open import Ch2.Homotopy-type-theory
open import Ch3.Sets-and-logic
open import Ch4.Equivalences
open import Ch5.1-Introduction-to-inductive-types

module Ch6.11-Algebra where


-- List concatenation

_++_ : {A : 𝓤 ̇} → List A → List A → List A
nil ++ l = l
(a ∷ l₁) ++ l₂ = a ∷ (l₁ ++ l₂)

infixr 30 _++_


-- Theorem 6.11.7 (Concrete definition of free group).

module _ (𝓤 : Universe) (A : 𝓤 ̇) (i : isSet A) where

  R : List (A + A) → List (A + A) → 𝓤 ̇
  R l₁ l₂ = Σ a ꞉ A , Σ l₃ ꞉ List (A + A) , Σ l₄ ꞉ List (A + A) , ((l₁ ≡ l₃ ++ (inl a ∷ (inr a ∷ l₄))) + ((l₁ ≡ l₃ ++ (inr a ∷ (inl a ∷ l₄))))) × (l₂ ≡ l₃ ++ l₄)

  -- Alternative: define R as inductive type rather than using pi , sigma and id types:

  data R' : List (A + A) → List (A + A) → 𝓤 ̇ where
    ri : (a : A) (l₁ : List (A + A)) (l₂ : List (A + A)) → R' (l₁ ++ ((inl a) ∷ ((inr a) ∷ l₂))) (l₁ ++ l₂)
    li : (a : A) (l₁ : List (A + A)) (l₂ : List (A + A)) → R' (l₁ ++ ((inr a) ∷ ((inl a) ∷ l₂))) (l₁ ++ l₂)

  R-lemma : (l₁ l₂ : List (A + A)) → R l₁ l₂ ⇔ R' l₁ l₂
  R-lemma l₁ l₂ = R-to-R' l₁ l₂ , R'-to-R l₁ l₂
   where
   R-to-R' : (l₁ l₂ : List (A + A)) → R l₁ l₂ → R' l₁ l₂
   R-to-R' .(l₃ ++ (inl a ∷ (inr a ∷ l₄))) .(l₃ ++ l₄) (a , l₃ , l₄ , inl (refl .(l₃ ++ (inl a ∷ (inr a ∷ l₄)))) , refl .(l₃ ++ l₄)) = ri a l₃ l₄
   R-to-R' .(l₃ ++ (inr a ∷ (inl a ∷ l₄))) .(l₃ ++ l₄) (a , l₃ , l₄ , inr (refl .(l₃ ++ (inr a ∷ (inl a ∷ l₄)))) , refl .(l₃ ++ l₄)) = li a l₃ l₄
   R'-to-R : (l₁ l₂ : List (A + A)) → R' l₁ l₂ → R l₁ l₂
   R'-to-R .(l₁ ++ (inl a ∷ (inr a ∷ l₂))) .(l₁ ++ l₂) (ri a l₁ l₂) = a , l₁ , l₂ , inl (refl _) , refl _
   R'-to-R .(l₁ ++ (inr a ∷ (inl a ∷ l₂))) .(l₁ ++ l₂) (li a l₁ l₂) = a , l₁ , l₂ , inr (refl _) , refl _  

  -- Problem: need to characterize identity type of this new type to show that it is a mere relation (on top of proving the correctness of the characterization).
  -- Benefit: pattern-matching

{-  

data T : A → A → 𝓤
  cons1 : (x y : A) → Π₁ B (g x , g y) → T x y -- triples (x , q , y)
  cons2 : (w x y z : A) → T w x → T y z → Π₁ B (f x , f y) → T w z -- glueing tryples via p's

data code (i b, i b') : 𝓤
  cons3 : Π₁ B (b , b') -- triples (b , p₀ , b')
  cons4 : (x y : A) → Π₁ B (b , f x) → Π₁ B (f y , b') → code (i b , i b') -- sequence (b , p₀ , x , ... y , pₙ , b')

-}

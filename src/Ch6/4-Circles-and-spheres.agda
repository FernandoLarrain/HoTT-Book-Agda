{-# OPTIONS --without-K --exact-split --rewriting #-}

open import Ch1.Type-theory
open import Ch2.Homotopy-type-theory
open import Ch3.Sets-and-logic
open import Ch4.Equivalences
open import Rewrite
open import Ch6.2-Induction-pples-and-dependent-paths

module Ch6.4-Circles-and-spheres where


module _ (univ : Univalence) where

  open Full-Univalence univ
  
  -- Lemma 6.4.1 (The circle is nontrivial).

  𝕊¹-is-nontrivial : ¬ (loop₁ ≡ refl base₁)
  𝕊¹-is-nontrivial s = 𝓤-is-not-Set univ 𝓤₀ λ x y p q → ∙ₗ-inv (q ⁻¹) p q (loop₁-β' y (q ⁻¹ ∙ p) ⁻¹ ∙ ap (ap (𝕊¹-rec y (q ⁻¹ ∙ p))) s ∙ (linv q ⁻¹))


  -- Lemma 6.4.2 (𝑖𝑑 𝕊¹ ∼ 𝑖𝑑 𝕊¹ has a nontrivial inhabitant).

  nontrivial-inhabitant : (x : 𝕊¹) → x ≡ x
  nontrivial-inhabitant = 𝕊¹-ind _ loop₁ (transport-loop loop₁ loop₁ ∙ ((linv _ ∙ᵣ loop₁) ∙ lu _ ⁻¹))

  nontrivial-inhabitant-is-nontrivial : ¬ (nontrivial-inhabitant ≡ hrefl _)
  nontrivial-inhabitant-is-nontrivial p = 𝕊¹-is-nontrivial (happly p base₁)


  -- Lemma 6.4.3 (A universe with circle is not a 1-type).

  𝓤₀-is-not-⟨1⟩-type : ¬ (is-⟨1⟩-type (𝓤₀ ̇))
  𝓤₀-is-not-⟨1⟩-type i = nontrivial-inhabitant-is-nontrivial (k _ _) where
    aux-equiv : (≃-refl 𝕊¹ ≡ ≃-refl 𝕊¹) ≃ (𝑖𝑑 𝕊¹ ∼ 𝑖𝑑 𝕊¹)
    aux-equiv =
      (≃-refl 𝕊¹ ≡ ≃-refl 𝕊¹)
        ≃⟨ Σ-over-predicate' ishae-is-Prop _ _ ⟩
      (𝑖𝑑 𝕊¹ ≡ 𝑖𝑑 𝕊¹)
        ≃⟨ happly , happly-is-equiv ⟩
      (𝑖𝑑 𝕊¹ ∼ 𝑖𝑑 𝕊¹) ■
    j : isSet (𝕊¹ ≃ 𝕊¹ )
    j = ≃-preserves-Sets (idtoeqv , idtoeqv-is-equiv) (i _ _)
    k : isProp (𝑖𝑑 𝕊¹ ∼ 𝑖𝑑 𝕊¹)
    k = ≃-preserves-Props aux-equiv (j _ _)

  -- TO DO: Lift to arbitrary universes.


-- Lemmas 6.4.4-6:

open import Ch6.4-Circles-and-spheres-safe public


{- Note: There's a slight inconsistency in the book. Let f = 𝕊²-ind. Then, 
  
  apd² f surf : adp f (refl base₂) ≡ apd f (refl base₂) [ P ⇊ surf ] , 

while 
  
  s : refl b ≡ refl b [ (λ p → b ≡ b [ P ↓ p ] ↓ surf ] .

As shown in Ch6.Exercises, these two types are equal, but not judgmentally. In what follows, we adopt PathOver² as our official definition. -}


-- The Sphere, 𝕊².

postulate

  -- (i) Type formation rule

  𝕊² : 𝓤₀ ̇

  -- (ii) Constructors
  
  base₂ : 𝕊²
  surf : refl base₂ ≡ refl base₂

module _ (P : 𝕊² → 𝓤 ̇) (b : P base₂) (s : refl b ≡ refl b [ P ⇊ surf ]) where

  postulate

    -- (iii) Induction principle

    𝕊²-ind : Π P
  
    -- (iv) Computation rules

    base₂-β : 𝕊²-ind base₂ ↦ b

    {-# REWRITE base₂-β #-}

    surf-β : apd² 𝕊²-ind surf ≡ s

module _ {B : 𝓤 ̇} (b : B) (s : refl b ≡ refl b) where

  -- (v) Recursion principle
  
  𝕊²-rec : 𝕊² → B
  𝕊²-rec = 𝕊²-ind (λ x → B) b (s ∙ (transport²const B surf b ⁻¹ ∙ ru _))

  -- (vi) Computation rules
  
  base₂-β' : 𝕊²-rec base₂ ≡ b
  base₂-β' = refl _

  surf-β' : ap² 𝕊²-rec surf ≡ s
  surf-β' =  ru _ ∙ lu _ ∙ ru _ ∙ lu _ ∙ ru _ ∙ ∙ᵣ-inv _ _ _ (ap (λ - → refl (refl (𝕊²-rec base₂)) ∙ (refl (refl (𝕊²-rec base₂)) ∙ (ap² 𝕊²-rec surf ∙ refl (refl (𝕊²-rec base₂))) ∙ refl (refl (𝕊²-rec base₂))) ∙ refl (refl (𝕊²-rec base₂)) ∙ (- ∙ ru (transport² (λ a → B) surf (𝕊²-rec base₂)))) (lu (transport²const B surf (𝕊²-rec base₂) ⁻¹)) ∙ (apd²-const B 𝕊²-rec surf ⁻¹ ∙ surf-β (λ x → B) b (s ∙ (transport²const B surf b ⁻¹ ∙ ru _))))

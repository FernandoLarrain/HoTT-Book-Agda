{-# OPTIONS --without-K --exact-split --safe #-}

open import Ch1.Type-theory
open import Ch2.Homotopy-type-theory
open import Ch3.Sets-and-logic
open import Ch4.Equivalences

module Ch6.5-Suspensions-safe where


-- Definition (adjoining a disjoint basepoint).

_₊ : (A : 𝓤 ̇) → 𝓤 ⊙
A ₊ = ((A + 𝟙) , inr ⋆)


-- Lemma 6.5.3.

module based-maps-≃-unbased-maps ⦃ fe : FunExt ⦄ (A : 𝓤 ̇) (B' : 𝓥 ⊙) where

  B = pr₁ B'
  b₀ = pr₂ B'

  from-based-maps : Map⊙ (A ₊) B' → (A → B)
  from-based-maps (f , p) = f ∘ inl

  to-based-maps : (A → B) →  Map⊙ (A ₊) B'
  to-based-maps g = (+-recursion g (λ u → b₀)) , (refl b₀)

  from∘to : from-based-maps ∘ to-based-maps ∼ id
  from∘to g = funext λ a → refl (g a)
 
  to∘from : to-based-maps ∘ from-based-maps ∼ id
  to∘from (f , p) = dpair-≡ (
      q ,
      (
      transport (λ - → - (inr ⋆) ≡ b₀) q (refl b₀)
        ≡⟨ transport-funval-≡' (inr ⋆) b₀ q (refl b₀) ⟩
      happly q (inr ⋆) ⁻¹ ∙ refl b₀
        ≡⟨ ru _ ⁻¹ ⟩
      happly q (inr ⋆) ⁻¹
        ≡⟨ ap _⁻¹ (happly-β _ (inr ⋆)) ⟩
      (p ⁻¹) ⁻¹
        ≡⟨ ⁻¹-invol _ ⟩
      p ∎
      )
    )
    where
    q : +-recursion (f ∘ inl) (λ u → b₀) ≡ f 
    q = funext (+-induction _ (λ a → refl (f (inl a))) (𝟙-induction _ (p ⁻¹))) 
  equivalence : Map⊙ (A ₊) B' ≃ (A → B)
  equivalence = from-based-maps , qinv-to-isequiv (to-based-maps , from∘to , to∘from)


-- Points of a type

points-of-a-type : ⦃ fe : FunExt ⦄ (A : 𝓤 ̇) → (𝟙 → A) ≃ A
points-of-a-type A = (λ f → f ⋆) , qinv-to-isequiv ((λ a u → a) , (refl , λ f → funext (𝟙-induction _ (refl (f ⋆))))) 

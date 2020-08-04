{-# OPTIONS --without-K --exact-split --safe #-}

open import Ch1.Type-theory
open import Ch2.Homotopy-type-theory

module Ch3.2-Propositions-as-types where


-- Theorem 3.2.2 (DNE is incompatible with univalence).

DNE∞ : (𝓤 : Universe) →  𝓤 ⁺ ̇
DNE∞ 𝓤 = (A : 𝓤 ̇) → ¬ (¬ A) → A  

module not-DNE∞ ⦃ fe : FunExt ⦄ ⦃ univ : Univalence ⦄ where

  -- (i) Some auxiliary lemmas:
  
  ¬¬𝟚-is-Prop : (u v : ¬ (¬ 𝟚)) → u ≡ v
  ¬¬𝟚-is-Prop u v = funext λ x → !𝟘 _ (u x)

  𝟚-is-nonempty : ¬ (is-empty 𝟚)
  𝟚-is-nonempty x = x ₀

  -- (ii) Define autoequivalence of 𝟚 with no fixed point

  f : 𝟚 → 𝟚
  f ₀ = ₁
  f ₁ = ₀

  f-has-no-fixed-pt : (x : 𝟚) → ¬ (f x ≡ x)
  f-has-no-fixed-pt ₀ c = ₀-is-not-₁ (c ⁻¹)
  f-has-no-fixed-pt ₁ c = ₀-is-not-₁ c

  swap-equiv : 𝟚 ≃ 𝟚
  swap-equiv =
    f ,
    qinv-to-isequiv (
      f ,
      (𝟚-induction _ (refl _) (refl _)) ,
      (𝟚-induction _ (refl _) (refl _))
      ) 

  -- (iii) DNE∞ gives fixed point

  DNE∞-gives-fixed-pt : DNE∞ 𝓤₀ → Σ x ꞉ 𝟚 , f x ≡ x
  DNE∞-gives-fixed-pt dne = x , x-is-fixed-pt where
    p : 𝟚 ≡ 𝟚
    p = ua swap-equiv
    x : 𝟚
    x = dne 𝟚 𝟚-is-nonempty
    y : 𝟚
    y = dne 𝟚 (transport (λ - → ¬ (¬ -)) (p ⁻¹) 𝟚-is-nonempty)
    x-is-fixed-pt : f x ≡ x
    x-is-fixed-pt =
      f x
        ≡⟨ idtoeqv-β swap-equiv x ⁻¹ ⟩
      coe p x
        ≡⟨ ap (coe p ∘ dne 𝟚) (¬¬𝟚-is-Prop _ _) ⟩
      coe p y
        ≡⟨ transport-fun p (dne 𝟚) 𝟚-is-nonempty ⁻¹ ⟩
      transport (λ - → ¬ (¬ -) → -) p (dne 𝟚) 𝟚-is-nonempty 
        ≡⟨ happly (apd dne p) 𝟚-is-nonempty  ⟩
      x ∎
      
  -- (iii) The theorem:
  
  not-DNE∞ : ¬ (DNE∞ 𝓤₀)
  not-DNE∞ dne with DNE∞-gives-fixed-pt dne
  ... | (x , x-is-fixed-pt) = f-has-no-fixed-pt x x-is-fixed-pt

open not-DNE∞ using (not-DNE∞)

-- Corollary 3.2.7 (LEM is incompatible with univalence).

LEM∞ : (𝓤 : Universe) → 𝓤 ⁺ ̇
LEM∞ 𝓤 = (A : 𝓤 ̇) → A + ¬ A

not-LEM∞ : ⦃ fe : FunExt ⦄ ⦃ univ : Univalence ⦄ → ¬ (LEM∞ 𝓤₀)
not-LEM∞ lem = not-DNE∞ (λ A → +-recursion (λ a f → a) (λ w f → !𝟘 _ (f w)) (lem A))


-- Remark 3.2.6 ("Triple negation law" is compatible with univalence).

TNL∞ : (𝓤 : Universe) → 𝓤 ⁺ ̇
TNL∞ 𝓤 = (A : 𝓤 ̇) → ¬ (¬ (¬ A)) → ¬ A

TNL∞-holds : TNL∞ 𝓤
TNL∞-holds A f a = f (λ g → g a)


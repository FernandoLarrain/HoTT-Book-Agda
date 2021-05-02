{-# OPTIONS --without-K --exact-split --safe #-}

open import Ch1.Type-theory
open import Ch2.Homotopy-type-theory

module Ch3.2-Propositions-as-types (univ : Univalence) where

open Basic-Univalence univ


-- Theorem 3.2.2 (DNE is incompatible with univalence).

DNE∞ : (𝓤 : Universe) →  𝓤 ⁺ ̇
DNE∞ 𝓤 = (A : 𝓤 ̇) → ¬ (¬ A) → A  

module not-DNE∞ ⦃ fe : FunExt ⦄ where

  -- (i) Some auxiliary lemmas:
  
  ¬¬𝟚-is-Prop : (u v : ¬ (¬ 𝟚)) → u ≡ v
  ¬¬𝟚-is-Prop u v = funext λ x → !𝟘 _ (u x)

  𝟚-is-nonempty : ¬ (is-empty 𝟚)
  𝟚-is-nonempty x = x ₀

  -- (ii) Define autoequivalence of 𝟚 with no fixed point

  twist : 𝟚 → 𝟚
  twist ₀ = ₁
  twist ₁ = ₀

  twist-has-no-fixed-pt : (x : 𝟚) → ¬ (twist x ≡ x)
  twist-has-no-fixed-pt ₀ c = ₀-is-not-₁ (c ⁻¹)
  twist-has-no-fixed-pt ₁ c = ₀-is-not-₁ c

  twist-≃ : 𝟚 ≃ 𝟚
  twist-≃ =
    twist ,
    qinv-to-isequiv (
      twist ,
      (𝟚-induction _ (refl _) (refl _)) ,
      (𝟚-induction _ (refl _) (refl _))
      ) 

  -- (iii) DNE∞ gives fixed point

  DNE∞-gives-fixed-pt : DNE∞ 𝓤₀ → Σ x ꞉ 𝟚 , twist x ≡ x
  DNE∞-gives-fixed-pt dne = x , x-is-fixed-pt where
    p : 𝟚 ≡ 𝟚
    p = ua twist-≃
    x : 𝟚
    x = dne 𝟚 𝟚-is-nonempty
    y : 𝟚
    y = dne 𝟚 (transport (λ - → ¬ (¬ -)) (p ⁻¹) 𝟚-is-nonempty)
    x-is-fixed-pt : twist x ≡ x
    x-is-fixed-pt =
      twist x
        ≡⟨ idtoeqv-β twist-≃ x ⁻¹ ⟩
      coe p x
        ≡⟨ ap (coe p ∘ dne 𝟚) (¬¬𝟚-is-Prop _ _) ⟩
      coe p y
        ≡⟨ transport-fun p (dne 𝟚) 𝟚-is-nonempty ⁻¹ ⟩
      transport (λ - → ¬ (¬ -) → -) p (dne 𝟚) 𝟚-is-nonempty 
        ≡⟨ happly (apd dne p) 𝟚-is-nonempty  ⟩
      x ∎
      
  -- (iii) The theorem:
  
  not-DNE∞ : ¬ (DNE∞ 𝓤₀)
  not-DNE∞ dne = twist-has-no-fixed-pt (pr₁ (DNE∞-gives-fixed-pt dne)) (pr₂ (DNE∞-gives-fixed-pt dne))

open not-DNE∞ using (not-DNE∞)

-- Corollary 3.2.7 (LEM is incompatible with univalence).

LEM∞ : (𝓤 : Universe) → 𝓤 ⁺ ̇
LEM∞ 𝓤 = (A : 𝓤 ̇) → A + ¬ A

not-LEM∞ : ⦃ fe : FunExt ⦄ → ¬ (LEM∞ 𝓤₀)
not-LEM∞ lem = not-DNE∞ (λ A → +-recursion (λ a f → a) (λ w f → !𝟘 _ (f w)) (lem A))


-- Remark 3.2.6 ("Triple negation law" is compatible with univalence).

TNL∞ : (𝓤 : Universe) → 𝓤 ⁺ ̇
TNL∞ 𝓤 = (A : 𝓤 ̇) → ¬ (¬ (¬ A)) → ¬ A

TNL∞-holds : TNL∞ 𝓤
TNL∞-holds A f a = f (λ g → g a)


{-# OPTIONS --without-K --exact-split --safe #-}

open import Ch1.Type-theory
open import Ch2.Homotopy-type-theory

module Ch3.1-Sets-and-n-types where


-- Definition 3.1.1 (Set).

isSet : 𝓤 ̇ → 𝓤 ̇
isSet A = (x y : A) (p q : x ≡ y) → p ≡ q


-- Example 3.1.2 (𝟙 is a set).

𝟙-is-Set : isSet 𝟙
𝟙-is-Set x y p q =
  p
    ≡⟨ 𝟙-≡-η p ⁻¹ ⟩
  𝟙-to-≡ (≡-to-𝟙 p)
    ≡⟨ refl _ ⟩
  𝟙-to-≡ (≡-to-𝟙 q)
    ≡⟨ 𝟙-≡-η q ⟩
  q ∎


-- Example 3.1.3 (𝟘 is a set).

𝟘-is-Set : isSet 𝟘
𝟘-is-Set = 𝟘-induction _


-- Example 3.1.4 (ℕ is a set).

ℕ-is-Set : isSet ℕ
ℕ-is-Set m n p q =
  p
    ≡⟨ (path-space-ℕ'' m n p) ⁻¹ ⟩
  decode-ℕ m n (encode-ℕ m n p)
    ≡⟨ ap (decode-ℕ m n) (code-ℕ-is-Prop m n _ _) ⟩
  decode-ℕ m n (encode-ℕ m n q)
    ≡⟨ path-space-ℕ'' m n q ⟩
  q ∎


-- Example 3.1.5 (_×_ preserves sets).

×-preserves-Sets : {A : 𝓤 ̇} {B : 𝓥 ̇} → isSet A → isSet B → isSet (A × B)
×-preserves-Sets f g (x , y) (z , w) p q = ×-≡-η p ⁻¹ ∙ ap pair-≡ (ap (λ - → - , ap pr₂ p) (f x z _ _) ∙ ap (λ - → ap pr₁ q , -) (g y w _ _)) ∙ ×-≡-η q

Σ-preserves-Sets : {A : 𝓤 ̇} {P : A → 𝓥 ̇} → isSet A → ((x : A) → isSet (P x)) → isSet (Σ P)
Σ-preserves-Sets {𝓤} {𝓥} {A} {P} f g (z₁ , z₂) (w₁ , w₂) p q = Σ-≡-η p ⁻¹ ∙ ap dpair-≡ (dpair-≡ (f z₁ w₁ _ _ , g w₁ _ w₂ _ _)) ∙ Σ-≡-η q


-- Example 3.1.6 (Π preserves sets).

Π-preserves-Sets : ⦃ fe : FunExt ⦄ {A : 𝓤 ̇} {P : A → 𝓥 ̇} → ((x : A) → isSet (P x)) → isSet (Π P)
Π-preserves-Sets i f g p q = happly-η p ⁻¹ ∙ ap funext (funext (λ x → i x _ _ _ _)) ∙ happly-η q


-- Definition 3.1.7 (1-type).

is-⟨1⟩-type : 𝓤 ̇ → 𝓤 ̇
is-⟨1⟩-type A = (x y : A) (p q : x ≡ y) (r s : p ≡ q) → r ≡ s


-- Lemma 3.1.8. See Lemma 3.3.4.


-- Example 3.1.9 (Not all types are sets).

module 𝓤-is-not-Set ⦃ univ : Univalence ⦄ (𝓤 : Universe) where

  id-equiv : 𝟚 ≃ 𝟚
  id-equiv = 𝑖𝑑 𝟚 , qinv-to-isequiv (qinv-𝑖𝑑 𝟚)

  id-equiv' : Lift 𝓤 𝟚 ≃ Lift 𝓤 𝟚
  id-equiv' = Lift-≃ ● id-equiv ● ≃-Lift

  f : 𝟚 → 𝟚
  f ₀ = ₁
  f ₁ = ₀

  swap-equiv : 𝟚 ≃ 𝟚
  swap-equiv =
    f ,
    qinv-to-isequiv (
      f ,
      (𝟚-induction _ (refl _) (refl _)) ,
      (𝟚-induction _ (refl _) (refl _))
      ) 

  swap-equiv' : Lift 𝓤 𝟚 ≃ Lift 𝓤 𝟚
  swap-equiv' = Lift-≃ ● swap-equiv ● ≃-Lift

  ₀-is-not-₁' : ¬ (lift {𝓤₀} {𝓤} ₀ ≡ lift {𝓤₀} {𝓤} ₁)
  ₀-is-not-₁' p = ₀-is-not-₁ (ap lower p)

  𝓤-is-not-Set : ¬ (isSet (𝓤 ̇))
  𝓤-is-not-Set g =
    let p : id-equiv' ≡ swap-equiv'
        p = idtoeqv-β' id-equiv' ⁻¹ ∙ ap idtoeqv (g (Lift 𝓤 𝟚) (Lift 𝓤 𝟚) (ua id-equiv') (ua swap-equiv')) ∙ idtoeqv-β' (swap-equiv')
    in ₀-is-not-₁' (transport (λ (- : Lift 𝓤 𝟚 → Lift 𝓤 𝟚) → lift ₀ ≡ - (lift ₀)) (ap pr₁ p) (refl (lift ₀)))

open 𝓤-is-not-Set using (𝓤-is-not-Set) public

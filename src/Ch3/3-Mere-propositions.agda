{-# OPTIONS --without-K --exact-split --safe #-}

open import Ch1.Type-theory
open import Ch2.Homotopy-type-theory
open import Ch3.1-Sets-and-n-types

module Ch3.3-Mere-propositions where


-- Definition 3.3.1 (Proposition).

isProp : 𝓤 ̇ → 𝓤 ̇
isProp P = (x y : P) → x ≡ y

𝟘-is-Prop : isProp (𝟘)
𝟘-is-Prop = λ x → 𝟘-induction (λ x → (y : 𝟘) → x ≡ y) x


-- Lemma 3.3.2.: After Lemma 3.3.3.


-- Lemma 3.3.3 (Logically equivalent propositions are equivalent).

⇔-to-≃ : {P : 𝓤 ̇} {Q : 𝓥 ̇} → isProp P → isProp Q → (P ⇔ Q) → P ≃ Q
⇔-to-≃ p q (f , g) = f , qinv-to-isequiv (g , (λ x → q _ _) , (λ x → p _ _))

≃-to-⇔ : {P : 𝓤 ̇} {Q : 𝓥 ̇} → (P ≃ Q) → (P ⇔ Q)
≃-to-⇔ e = pr₁ e , inv e

{- Note: the actual equivalence is proved in Ch7.1 -}


-- Lemma 3.3.2 (Inhabited propositions are 𝟙).

inhabited-Prop-is-𝟙 : {P : 𝓤 ̇} → isProp P → (x₀ : P) → P ≃ 𝟙
inhabited-Prop-is-𝟙 P-is-Prop x₀ = ⇔-to-≃ P-is-Prop 𝟙-is-Prop ((λ x → ⋆) , λ x → x₀)


-- Lemma 3.3.4 (Propositions are sets).

isProp-to-isSet : {A : 𝓤 ̇} → isProp A → isSet A
isProp-to-isSet {𝓤} {A} f x y p q =
  p
    ≡⟨ ii x y p ⟩
  g x ⁻¹ ∙ g y
    ≡⟨ ii x y q ⁻¹ ⟩ 
  q ∎
  where
  g : (y : A) → x ≡ y
  g y = f x y
  i : (y z : A) → (p : y ≡ z) → g y ∙ p ≡ g z
  i y z p =
    g y ∙ p
      ≡⟨ transport-post-∙ p (g y) ⁻¹ ⟩
    transport (λ - → x ≡ -) p (g y)
      ≡⟨ apd g p ⟩
    g z ∎
  ii : (y z : A) → (p : y ≡ z) → p ≡ g y ⁻¹ ∙ g z
  ii y z p =
    p
      ≡⟨ lu p ⟩
    refl y ∙ p
      ≡⟨ ap (λ - → - ∙ p) (linv (g y) ⁻¹) ⟩
    g y ⁻¹ ∙ g y ∙ p
      ≡⟨ ∙-assoc _ _ _ ⁻¹ ⟩
    g y ⁻¹ ∙ (g y ∙ p)
      ≡⟨ ap (λ - → ((g y) ⁻¹) ∙ -) (i y z p) ⟩
    g y ⁻¹ ∙ g z ∎


-- Lemma 3.1.8 (Sets are 1-types).

isSet-to-is-⟨1⟩-type : (A : 𝓤 ̇) → isSet A → is-⟨1⟩-type A
isSet-to-is-⟨1⟩-type A f x y = isProp-to-isSet (f x y)


-- Lemma 3.3.5.

module _  ⦃ fe : FunExt ⦄ where

  isProp-is-Prop : (A : 𝓤 ̇) → isProp (isProp A)
  isProp-is-Prop A f g = funext (λ x → funext (λ y → isProp-to-isSet f x y (f x y) (g x y)))

  isSet-is-Prop : (A : 𝓤 ̇) → isProp (isSet A)
  isSet-is-Prop A f g =
    funext (λ a →
      funext (λ b →
        funext (λ p →
          funext (λ q →
            isSet-to-is-⟨1⟩-type A f a b p q (f a b p q) (g a b p q)
          )
        )
      )
    )

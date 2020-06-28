{-# OPTIONS --without-K --exact-split --safe #-}

open import Ch1.Type-theory
open import Ch2.4-Homotopies-and-equivalences

module Ch2.8-The-unit-type where


-- Theorem 2.8.1 (Path-space of 𝟙 is 𝟙).

≡-to-𝟙 : {x y : 𝟙} → x ≡ y → 𝟙
≡-to-𝟙 p = ⋆

𝟙-to-≡ : {x y : 𝟙} → 𝟙 → x ≡ y
𝟙-to-≡ {⋆} {⋆} u = refl ⋆

𝟙-≡-β : {x y : 𝟙} (u : 𝟙) → ≡-to-𝟙 (𝟙-to-≡ {x} {y} u) ≡ u
𝟙-≡-β ⋆ = refl ⋆

𝟙-≡-η : {x y : 𝟙} (p : x ≡ y) → 𝟙-to-≡ (≡-to-𝟙 p) ≡ p
𝟙-≡-η (refl ⋆) = refl (refl ⋆)

𝟙-≡-≃-𝟙 : (x y : 𝟙) → (x ≡ y) ≃ 𝟙
𝟙-≡-≃-𝟙 x y = ≡-to-𝟙 , qinv-to-isequiv (𝟙-to-≡ , (𝟙-≡-β {x} {y} , 𝟙-≡-η))

𝟙-is-Prop : (x y : 𝟙) → x ≡ y
𝟙-is-Prop x y = 𝟙-to-≡ ⋆

{- Note: for the meaning of "Prop", see Def. 3.3.1 (isProp) in 3-Mere-propositions. -}

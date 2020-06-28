{-# OPTIONS --without-K --exact-split --safe #-}

open import Ch1.Type-theory
open import Ch2.1-Types-are-higher-groupoids

module Ch2.2-Functions-are-functors where


-- Lemma 2.2.1 (Action on paths).

ap : {A : 𝓤 ̇ } {B : 𝓥 ̇ } (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
ap f (refl x) = refl (f x)


-- Theorem 2.1.6 (Eckmann-Hilton continued).

eckmann-hilton : {A : 𝓤 ̇ } {a : A} (α β : refl a ≡ refl a) → (α ∙ β) ≡ (β ∙ α)
eckmann-hilton {a = a} α β = ((u ⁻¹) ∙ (hz-agreement α β) ) ∙ v where
  u : (α ⋆' β) ≡ (α ∙ β)
  v : (α ⋆'' β) ≡ (β ∙ α)
  u = ap (_∙ _) (ru _ ⁻¹ ∙ lu _ ⁻¹) ∙ ∙-assoc _ _ _ ∙ (ru _ ⁻¹ ∙ ap (α ∙_) (lu _ ⁻¹))
  v = ap (_∙ _) (ru _ ⁻¹ ∙ lu _ ⁻¹) ∙ ∙-assoc _ _ _ ∙ (ru _ ⁻¹ ∙ ap (β ∙_) (lu _ ⁻¹))


-- Lemma 2.2.2 (ap is functorial).

ap-∙ : {A : 𝓤 ̇ } {B : 𝓥 ̇ } {x y z : A} (f : A → B) (p : x ≡ y) (q : y ≡ z) → (ap f (p ∙ q)) ≡ ((ap f p) ∙ (ap f q))
ap-∙ f (refl .x) (refl x) = refl (refl (f x))

ap-⁻¹ : {A : 𝓤 ̇ } {B : 𝓥 ̇ } {x y : A} (f : A → B) (p : x ≡ y) → ap f (p ⁻¹) ≡ ap f p ⁻¹
ap-⁻¹ f (refl x) = refl (refl (f x))

ap-∘ : {A : 𝓤 ̇ } {B : 𝓥 ̇ } {C : 𝓦 ̇ } {x y : A} (f : A → B) (g : B → C) (p : x ≡ y) → ap g (ap f p) ≡ ap (g ∘ f) p
ap-∘ f g (refl x) = refl (refl (g (f x)))

ap-id : {A : 𝓤 ̇ } {x y : A} (p : x ≡ y) → ap id p ≡ p
ap-id (refl x) = refl (refl x)





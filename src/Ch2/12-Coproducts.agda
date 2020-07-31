{-# OPTIONS --without-K --exact-split #-}

open import Ch1.Type-theory
open import Ch2.1-Types-are-higher-groupoids
open import Ch2.2-Functions-are-functors
open import Ch2.3-Type-families-are-fibrations
open import Ch2.4-Homotopies-and-equivalences
open import Ch2.11-Identity-type

module Ch2.12-Coproducts where


-- Theorem 2.12.5 (Path-space of _+_).

-- (i) Setting up encode-decode

codel+ : {A : 𝓤 ̇} (B : 𝓥 ̇) (a₀ : A) → A + B → 𝓤 ̇
codel+ B a₀ (inl a) = a₀ ≡ a
codel+ {𝓤} B a₀ (inr b) = Lift 𝓤 𝟘

coder+ : (A : 𝓤 ̇) {B : 𝓥 ̇} (b₀ : B) → A + B → 𝓥 ̇
coder+ A b₀ (inr b) = b₀ ≡ b
coder+ {𝓤} {𝓥} A b₀ (inl a) = Lift 𝓥 𝟘

encodel+ : {A : 𝓤 ̇} {B : 𝓥 ̇} (a₀ : A) (x : A + B) → inl a₀ ≡ x → codel+ B a₀ x
encodel+ {B = B} a₀ x p = transport (codel+ B a₀) p (refl a₀)

encoder+ : {A : 𝓤 ̇} {B : 𝓥 ̇} (b₀ : B) (x : A + B) → inr b₀ ≡ x → coder+ A b₀ x
encoder+ {A = A} b₀ x p = transport (coder+ A b₀) p (refl b₀)

decodel+ : {A : 𝓤 ̇} {B : 𝓥 ̇} (a₀ : A) (x : A + B) → codel+ B a₀ x → inl a₀ ≡ x
decodel+ {B = B} a₀ (inl a) c = ap inl c

decoder+ : {A : 𝓤 ̇} {B : 𝓥 ̇} (b₀ : B) (x : A + B) → coder+ A b₀ x → inr b₀ ≡ x
decoder+ {A = A} b₀ (inr b) c = ap inr c

-- (ii) Characterization of left path space

path-space-inl : (A : 𝓤 ̇) (B : 𝓥 ̇) (a₀ : A) (x : A + B) → (inl a₀ ≡ x) ≃ codel+ B a₀ x
path-space-inl {𝓤} A B a₀ x = encodel+ a₀ x , qinv-to-isequiv ((decodel+ a₀ x) , (α , β))

  where
  
  α : (encodel+ a₀ x ∘ decodel+ a₀ x) ∼ id
  α = +-induction
    (λ x → (encodel+ a₀ x ∘ decodel+ a₀ x) ∼ id)
    (λ a c →
      encodel+ a₀ (inl a) (ap inl c)
        ≡⟨ transport-∘ (codel+ B a₀) inl c (refl a₀) ⁻¹ ⟩
      transport (λ - → a₀ ≡ -) c (refl a₀)
        ≡⟨ transport-post-∙ _ _ ⟩
      refl a₀ ∙ c
        ≡⟨ lu c ⁻¹ ⟩
      c ∎)
    (λ b → Lift-induction 𝓤 𝟘 (λ c → encodel+ a₀ (inr b) (decodel+ a₀ (inr b) c) ≡ c) (𝟘-induction _)) x

  β : (decodel+ a₀ x ∘ encodel+ a₀ x) ∼ id
  β = ℍ (inl a₀) (λ x p → decodel+ a₀ x (encodel+ a₀ x p) ≡ p) (refl (refl (inl a₀))) x

-- (iii) Characterization of right path space

path-space-inr : (A : 𝓤 ̇) (B : 𝓥 ̇) (b₀ : B) (x : A + B) → (inr b₀ ≡ x) ≃ coder+ A b₀ x
path-space-inr {𝓤} {𝓥} A B b₀ x = encoder+ b₀ x , qinv-to-isequiv ((decoder+ b₀ x) , (α , β))

  where

  α : (encoder+ b₀ x ∘ decoder+ b₀ x) ∼ id
  α = +-induction
    (λ x → (encoder+ b₀ x ∘ decoder+ b₀ x) ∼ id)
    (λ a → Lift-induction 𝓥 𝟘 (λ c → encoder+ b₀ (inl a) (decoder+ b₀ (inl a) c) ≡ c) (𝟘-induction _))
    (λ b c →
      encoder+ b₀ (inr b) (ap inr c)
        ≡⟨ (transport-∘ (coder+ A b₀) inr c (refl b₀)) ⁻¹ ⟩
      transport (λ - → b₀ ≡ -) c (refl b₀)
        ≡⟨ transport-post-∙ _ _ ⟩
      refl b₀ ∙ c
        ≡⟨ lu c ⁻¹ ⟩
      c ∎)
    x

  β : (decoder+ b₀ x ∘ encoder+ b₀ x) ∼ id
  β = ℍ (inr b₀) (λ x p → decoder+ b₀ x (encoder+ b₀ x p) ≡ p) (refl (refl (inr b₀))) x

+-is-disjoint : (A : 𝓤 ̇) (B : 𝓥 ̇) (a : A) (b : B) → ¬ (inl a ≡ inr b)
+-is-disjoint A B a b p = lower (encodel+ a (inr b) p)


-- Remark 2.12.6.

₀-is-not-₁ : ¬ (₀ ≡ ₁)
₀-is-not-₁ p = +-is-disjoint 𝟙 𝟙 ⋆ ⋆ p

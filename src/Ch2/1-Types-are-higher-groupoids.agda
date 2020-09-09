{-# OPTIONS --without-K --exact-split --safe #-}

open import Ch1.Type-theory

module Ch2.1-Types-are-higher-groupoids where


-- Lemma 2.1.1 (Inverse path).

_⁻¹ : {A : 𝓤 ̇} {x y : A} → x ≡ y → y ≡ x
refl x ⁻¹ = refl x

infix 40 _⁻¹


-- Lemma  2.1.2 (Path concatenation).

_∙_ : {A : 𝓤 ̇} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
refl x ∙ refl .x = refl x

infixl 30 _∙_


-- Equational reasoning with _≡_

_≡⟨_⟩_ : {X : 𝓤 ̇} (x : X) {y z : X} → x ≡ y → y ≡ z → x ≡ z
x ≡⟨ p ⟩ q = p ∙ q

infixr 0 _≡⟨_⟩_

_∎ : {X : 𝓤 ̇} (x : X) → x ≡ x
x ∎ = refl x

infix 1 _∎


-- Lemma 2.1.4 (Groupoid laws).

module _ {A : 𝓤 ̇} {x y : A} where 

  ru : (p : x ≡ y) → p ≡ p ∙ refl y
  ru (refl x) = refl (refl x)

  lu : (p : x ≡ y) → p ≡ refl x ∙ p
  lu (refl x) = refl (refl x)

  rinv : (p : x ≡ y) → p ∙ p ⁻¹ ≡ refl x
  rinv (refl x) = refl (refl x)

  linv : (p : x ≡ y) → p ⁻¹ ∙ p ≡ refl y
  linv (refl x) = refl (refl x)

  ⁻¹-invol : (p : x ≡ y) → (p ⁻¹) ⁻¹ ≡ p
  ⁻¹-invol (refl x) = refl (refl x)

∙-assoc : {A : 𝓤 ̇} {x y z w : A} (p : x ≡ y) (q : y ≡ z) (r : z ≡ w) → p ∙ (q ∙ r) ≡ p ∙ q ∙ r
∙-assoc (refl x) (refl x) (refl x) = refl (refl x)

-- A related law

distr : {A : 𝓤 ̇} {x y z : A} (p : x ≡ y) (q : y ≡ z) → (p ∙ q) ⁻¹ ≡ q ⁻¹ ∙ p ⁻¹
distr (refl _) (refl _) = refl _


-- Theorem 2.1.6 (Eckmann-Hilton).

module _ {A : 𝓤 ̇} {a b c : A} where

  -- Whiskering operations

  _∙ᵣ_ : {p q : a ≡ b} (α : p ≡ q) (r : b ≡ c) → p ∙ r ≡ q ∙ r
  _∙ᵣ_ {p} {q} α (refl b) = (ru p ⁻¹ ∙ α) ∙ ru q

  infix 30 _∙ᵣ_

  _∙ₗ_ : (q : a ≡ b) {r s : b ≡ c} (β : r ≡ s) → q ∙ r ≡ q ∙ s
  _∙ₗ_ (refl b) {r} {s} β = (lu r ⁻¹ ∙ β) ∙ lu s

  infix 30 _∙ₗ_

  -- Horizontal composition

  _✦_ : {p q : a ≡ b} {r s : b ≡ c} (α : p ≡ q) (β : r ≡ s) → p ∙ r ≡ q ∙ s
  _✦_ {q = q} {r = r} α β = (α ∙ᵣ r) ∙ (q ∙ₗ β)

  infixl 30 _✦_

  _✧_ : {p q : a ≡ b} {r s : b ≡ c} (α : p ≡ q) (β : r ≡ s) → (p ∙ r) ≡ (q ∙ s)
  _✧_ {p = p} {s = s} α β = (p ∙ₗ β) ∙ (α ∙ᵣ s)

  infixl 30 _✧_

  hz-comp-agreement : {p q : a ≡ b} {r s : b ≡ c} (α : p ≡ q) (β : r ≡ s) → (α ✦ β) ≡ (α ✧ β)
  hz-comp-agreement {refl x} {refl x} {refl x} {refl x} (refl (refl x)) (refl (refl x)) = refl (refl (refl x))

  {- For the proof of theorem, see next section, after Lemma 2.2.1 (Action on paths). The book proves Eckmann-Hilton before defining action on paths, but it is not clear how to do so without doing a path induction or using one of the asymmetric definitions of _∙_. -}


-- Definition 2.1.7 (pointed type).

_⊙ : (𝓤 : Universe) → 𝓤 ⁺ ̇
𝓤 ⊙ = Σ A ꞉ 𝓤 ̇ , A


-- Definition (based map).

Map⊙ : (A : 𝓤 ⊙) (B : 𝓥 ⊙) → 𝓤 ⊔ 𝓥 ̇
Map⊙ (A , a) (B , b) = Σ f ꞉ (A → B) , f a ≡ b 


-- Definition 2.1.8 (n-fold iterated loop space).

Ω : 𝓤 ⊙ → 𝓤 ⊙
Ω (A , a) = ((a ≡ a) , refl a)

Ω^ : ℕ → 𝓤 ⊙ → 𝓤 ⊙
Ω^ zero (A , a) = A , a
Ω^ (succ n) (A , a) = Ω^ n ( Ω (A , a)) -- inner loop

Ω'^ : ℕ → 𝓤 ⊙ → 𝓤 ⊙
Ω'^ zero (A , a) = (A , a)
Ω'^ (succ n) (A , a) = Ω (Ω^ n (A , a)) -- outer loop




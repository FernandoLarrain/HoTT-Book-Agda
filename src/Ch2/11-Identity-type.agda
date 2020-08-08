{-# OPTIONS --without-K --exact-split --safe #-}

open import Ch1.Type-theory
open import Ch2.1-Types-are-higher-groupoids
open import Ch2.2-Functions-are-functors
open import Ch2.3-Type-families-are-fibrations
open import Ch2.4-Homotopies-and-equivalences
open import Ch2.9-Π-types-and-funext

module Ch2.11-Identity-type where


-- Theorem 2.11.1 (The action on paths of an equivalence is an equivalence / Id preserves equivalence).

{- The proof is not hard; it is just a very long and detailed example of equational reasoning. It is easier to use the rewrite construct. -}

ap-of-equiv-is-equiv : {A : 𝓤 ̇} {B : 𝓥 ̇} {f : A → B} → isequiv (f) → (a a' : A) → isequiv (ap f {a} {a'})
ap-of-equiv-is-equiv {𝓤} {𝓥} {A} {B} {f} e a a' with isequiv-to-qinv e
... | (f⁻¹ , α , β) = qinv-to-isequiv (
  (λ q → β a ⁻¹ ∙ ap f⁻¹ q ∙ β a') ,
  (λ q → (
    ap f (β a ⁻¹ ∙ ap f⁻¹ q ∙ β a')
      ≡⟨ ap-id _ ⁻¹ ⟩
    ap (𝑖𝑑 B) (ap f (β a ⁻¹ ∙ ap f⁻¹ q ∙ β a'))
      ≡⟨ lu _ ⟩
    refl (f a) ∙ ap (𝑖𝑑 B) (ap f (β a ⁻¹ ∙ ap f⁻¹ q ∙ β a'))
      ≡⟨ ap (_∙ ap (𝑖𝑑 B) (ap f (β a ⁻¹ ∙ ap f⁻¹ q ∙ β a'))) (linv _ ⁻¹) ⟩
    α (f a) ⁻¹ ∙ α (f a) ∙ ap (𝑖𝑑 B) (ap f (β a ⁻¹ ∙ ap f⁻¹ q ∙ β a'))
      ≡⟨ ∙-assoc _ _ _ ⁻¹ ⟩
    α (f a) ⁻¹ ∙ (α (f a) ∙ ap (𝑖𝑑 B) (ap f (β a ⁻¹ ∙ ap f⁻¹ q ∙ β a')))
      ≡⟨ ap (α (f a) ⁻¹ ∙_) (hnat α _) ⟩
    α (f a) ⁻¹ ∙ (ap (f ∘ f⁻¹) (ap f (β a ⁻¹ ∙ ap f⁻¹ q ∙ β a')) ∙ α (f a'))
      ≡⟨ ap (λ - →  α (f a) ⁻¹ ∙ (- ∙ α (f a'))) (ap-∘ f⁻¹ f _ ⁻¹) ⟩
    α (f a) ⁻¹ ∙ (ap f (ap f⁻¹ (ap f (β a ⁻¹ ∙ ap f⁻¹ q ∙ β a'))) ∙ α (f a'))
      ≡⟨ ap (λ - → α (f a) ⁻¹ ∙ (ap f - ∙ α (f a'))) (ap-∘ f f⁻¹ _) ⟩
    α (f a) ⁻¹ ∙ (ap f (ap (f⁻¹ ∘ f) (β a ⁻¹ ∙ ap f⁻¹ q ∙ β a')) ∙ α (f a'))
      ≡⟨ ap (λ - → α (f a) ⁻¹ ∙ (ap f - ∙ α (f a'))) (
        ap (f⁻¹ ∘ f) (β a ⁻¹ ∙ ap f⁻¹ q ∙ β a')
          ≡⟨ ru _ ⟩
        ap (f⁻¹ ∘ f) (β a ⁻¹ ∙ ap f⁻¹ q ∙ β a') ∙ refl _
          ≡⟨ ap (ap (f⁻¹ ∘ f) (β a ⁻¹ ∙ ap f⁻¹ q ∙ β a') ∙_) (rinv (β a') ⁻¹) ⟩
        ap (f⁻¹ ∘ f) (β a ⁻¹ ∙ ap f⁻¹ q ∙ β a') ∙ (β a' ∙ β a' ⁻¹)
          ≡⟨ ∙-assoc _ _ _ ⟩
        ap (f⁻¹ ∘ f) (β a ⁻¹ ∙ ap f⁻¹ q ∙ β a') ∙ β a' ∙ β a' ⁻¹
          ≡⟨ ap (_∙ β a' ⁻¹) ((hnat β _) ⁻¹) ⟩
        β a ∙ ap (𝑖𝑑 A) (β a ⁻¹ ∙ ap f⁻¹ q ∙ β a') ∙ β a' ⁻¹
          ≡⟨ ap (λ - → β a ∙ - ∙ β a' ⁻¹) (ap-id _) ⟩
        β a ∙ (β a ⁻¹ ∙ ap f⁻¹ q ∙ β a') ∙ β a' ⁻¹
          ≡⟨ (∙-assoc _ _ _) ⁻¹ ⟩
        β a ∙ (β a ⁻¹ ∙ ap f⁻¹ q ∙ β a' ∙ β a' ⁻¹)
          ≡⟨ ap (β a ∙_) (∙-assoc _ _ _ ⁻¹) ⟩
        β a ∙ (β a ⁻¹ ∙ ap f⁻¹ q ∙ (β a' ∙ β a' ⁻¹))
          ≡⟨ ap (β a ∙_) ((ap (β a ⁻¹ ∙ ap f⁻¹ q ∙_) (rinv _)) ∙ ((ru _) ⁻¹)) ⟩
        (β a ∙ (β a ⁻¹ ∙ ap f⁻¹ q))
          ≡⟨ ∙-assoc _ _ _ ⟩
        (β a ∙ β a ⁻¹ ∙ ap f⁻¹ q)
          ≡⟨ (ap (_∙ ap f⁻¹ q) (rinv _) ∙ (lu _ ⁻¹)) ⟩
        (ap f⁻¹ q ∎)
        )    
      ⟩
    α (f a) ⁻¹ ∙ (ap f (ap f⁻¹ q) ∙ α (f a'))
      ≡⟨ ap (λ - → α (f a) ⁻¹ ∙ (- ∙ α (f a'))) (ap-∘ f⁻¹ f q) ⟩
    α (f a) ⁻¹ ∙ (ap (f ∘ f⁻¹) q ∙ α (f a'))
      ≡⟨ ap (α (f a) ⁻¹ ∙_) ((hnat α q) ⁻¹) ⟩
    α (f a) ⁻¹ ∙ (α (f a) ∙ ap (𝑖𝑑 B) q)
      ≡⟨ ∙-assoc _ _ _ ⟩
    α (f a) ⁻¹ ∙ α (f a) ∙ ap (𝑖𝑑 B) q
      ≡⟨ ap (_∙ ap (𝑖𝑑 B) q) (linv _) ⟩
    refl _ ∙ ap (𝑖𝑑 B) q
      ≡⟨ (lu _) ⁻¹ ⟩
    ap (𝑖𝑑 B) q
      ≡⟨ ap-id _ ⟩
    q ∎
  )) ,
  λ p → (
    β a ⁻¹ ∙ ap f⁻¹ (ap f p) ∙ β a'
      ≡⟨ ap (λ - → β a ⁻¹ ∙ - ∙ β a') (ap-∘ f f⁻¹ p) ⟩
    β a ⁻¹ ∙ ap (f⁻¹ ∘ f) p ∙ β a'
      ≡⟨ (∙-assoc _ _ _) ⁻¹ ⟩
    β a ⁻¹ ∙ (ap (f⁻¹ ∘ f) p ∙ β a')
      ≡⟨ ap (β a ⁻¹ ∙_) ((hnat β p) ⁻¹) ⟩
    β a ⁻¹ ∙ (β a ∙ ap (𝑖𝑑 A) p)
      ≡⟨ ∙-assoc _ _ _ ⟩
    β a ⁻¹ ∙ β a ∙ ap (𝑖𝑑 A) p
      ≡⟨ ap (_∙ ap (𝑖𝑑 A) p) (linv _) ⟩
    refl _ ∙ ap (𝑖𝑑 A) p
      ≡⟨ lu _ ⁻¹ ∙ ap-id _ ⟩
    p ∎
  ))


-- Example : ap lift and ap lower are equivalences.

ap-lift-is-equiv : {𝓥 : Universe} {A : 𝓤 ̇} {x y : A} → isequiv (ap (lift {𝓤} {𝓥} {A}) {x} {y})
ap-lift-is-equiv = ap-of-equiv-is-equiv (qinv-to-isequiv qinv-lift) _ _

ap-lower-is-equiv : {𝓥 : Universe} {A : 𝓤 ̇} {x y : Lift 𝓥 A} → isequiv (ap (lower {𝓤} {𝓥} {A}) {x} {y})
ap-lower-is-equiv = ap-of-equiv-is-equiv (qinv-to-isequiv qinv-lower) _ _


-- Lemma 2.11.2 (Transport of paths along equality of endpts).

transport-post-∙ : {A : 𝓤 ̇} {a x₁ x₂ : A} (p : x₁ ≡ x₂) (q : a ≡ x₁) → transport (λ - → a ≡ - ) p q ≡  (q ∙ p)
transport-post-∙ (refl _) = ru

transport-pre-∙ : {A : 𝓤 ̇} {a x₁ x₂ : A} (p : x₁ ≡ x₂) (q : x₁ ≡ a) → transport (λ - → - ≡ a ) p q ≡  p ⁻¹ ∙ q
transport-pre-∙ (refl _) = lu

transport-loop : {A : 𝓤 ̇} {x₁ x₂ : A} (p : x₁ ≡ x₂) (q : x₁ ≡ x₁) → transport (λ - → - ≡ - ) p q ≡  p ⁻¹ ∙ q ∙ p
transport-loop (refl x₁) q = q ≡⟨ ru q ⟩ q ∙ refl x₁ ≡⟨ ap (λ - → - ∙ refl x₁) (lu q) ⟩ refl x₁ ∙ q ∙ refl x₁ ∎


-- Theorem 2.11.3 (Transport of equality of function values along equality of inputs).

transport-funval-≡ : {A : 𝓤 ̇} {B : 𝓥 ̇} (f g : A → B) {a a' : A} (p : a ≡ a') (q : f a ≡ g a) → transport (λ - → f - ≡ g -) p q ≡ ap f p ⁻¹ ∙ q ∙ ap g p
transport-funval-≡ f g (refl x) q = ru q ∙ ap (_∙ refl (g x)) (lu q)

-- Transport of equality of function value along equality of functions

transport-funval-≡' : {A : 𝓤 ̇} {B : 𝓥 ̇} (a : A) (b : B) {f g : A → B} (p : f ≡ g) (q : f a ≡ b) → transport (λ - → - a ≡ b) p q ≡ happly p a ⁻¹ ∙ q
transport-funval-≡' a b (refl _) q = lu _


-- Theorem 2.11.4 (2.11.3 for dependent functions).

transport-dfunval-≡ : {A : 𝓤 ̇} {B : A → 𝓥 ̇} (f g : Π B) {a a' : A} (p : a ≡ a') (q : f a ≡ g a) → transport (λ - → f - ≡ g -) p q ≡ apd f p ⁻¹ ∙ ap (transport B p) q ∙ apd g p
transport-dfunval-≡ f g (refl x) q = ap-id q ⁻¹ ∙ ru _ ∙ ap (_∙ refl (g x)) (lu _)

transport-dfunval-≡' : {A : 𝓤 ̇} {B : A → 𝓥 ̇} (a : A) (b : B a) {f g : Π B} (p : f ≡ g) (q : f a ≡ b) → transport (λ - → - a ≡ b) p q ≡ happly p a ⁻¹ ∙ q
transport-dfunval-≡' a b (refl _) q = lu _


-- Theorem 2.11.5 (Dependent paths between loops)

dpath-space-loop : {A : 𝓤 ̇} {a a' : A} (p : a ≡ a') (q : a ≡ a) (r : a' ≡ a') → (transport (λ - → - ≡ -) p q ≡ r) ≃ (q ∙ p ≡ p ∙ r)
dpath-space-loop (refl x) q r =
  (λ s → ru q ⁻¹ ∙ s ∙ lu r) ,
  (qinv-to-isequiv (
    (λ s' → ru q ∙ (s' ∙ (lu r ⁻¹))) ,
    (λ s' →
      ru q ⁻¹ ∙ (ru q ∙ (s' ∙ lu r ⁻¹)) ∙ lu r
        ≡⟨ ap (_∙ lu r) (∙-assoc _ _ _) ⟩
      (ru q ⁻¹ ∙ ru q) ∙ (s' ∙ lu r ⁻¹) ∙ lu r
        ≡⟨ ap (λ - → - ∙ (s' ∙ lu r ⁻¹) ∙ lu r) (linv _) ∙ ap (_∙ lu r) (lu _ ⁻¹) ⟩
      s' ∙ lu r ⁻¹ ∙ lu r
        ≡⟨ (∙-assoc _ _ _ ⁻¹) ∙ ap (s' ∙_) (linv _) ∙ (ru _ ⁻¹) ⟩
      s' ∎
    ) ,
    λ s →
      ru q ∙ (ru q ⁻¹ ∙ s ∙ lu r ∙ lu r ⁻¹)
        ≡⟨ ap (ru q ∙_) (∙-assoc _ _ _ ⁻¹) ⟩
      ru q ∙ (ru q ⁻¹ ∙ s ∙ (lu r ∙ lu r ⁻¹))
        ≡⟨ ap (λ - → ru q ∙ (ru q ⁻¹ ∙ s ∙ -)) (rinv _) ⟩
      ru q ∙ (ru q ⁻¹ ∙ s ∙ refl _)
        ≡⟨ ap (ru q ∙_) (ru _ ⁻¹) ∙ ∙-assoc _ _ _  ⟩
      ru q ∙ ru q ⁻¹ ∙ s
        ≡⟨ ap (_∙ s) (rinv _) ∙ (lu _ ⁻¹)  ⟩
      s ∎
    )
  )

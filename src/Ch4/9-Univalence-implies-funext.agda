{-# OPTIONS --without-K --exact-split --safe #-}

open import Ch1.Type-theory
open import Ch2.Homotopy-type-theory
open import Ch3.Sets-and-logic
open import Ch4.2-Half-adjoint-equivalences
open import Ch4.4-Contractible-fibers
module Ch4.9-Univalence-implies-funext where


-- Definition 4.9.1 (The Weak Function Extensionality Principle).

weak-funext : {A : 𝓤 ̇} → (A → 𝓥 ̇) → 𝓤 ⊔ 𝓥 ̇
weak-funext P = Π (isContr ∘ P) → isContr (Π P)


-- Definition (Non-dependent Function Extensionality Principle).

non-dep-funext : (𝓤 𝓥 : Universe) → (𝓤 ⊔ 𝓥) ⁺ ̇ 
non-dep-funext 𝓤 𝓥 = {A : 𝓤 ̇} {B : 𝓥 ̇} {f g : A → B} → f ∼ g → f ≡ g


-- Lemma 4.9.2 (For a proof using function extensionality, see lemma 4.2.8 and exercise 2.17).

→-preserves-codom-≃' : is-univalent 𝓥 → (X : 𝓤 ̇) {A B : 𝓥 ̇} (e : A ≃ B) → isequiv {_} {_} {X → A} {X → B} (pr₁ e ∘_)
→-preserves-codom-≃' isuniv X {A} {B} e = transport (λ - → isequiv (- ∘_)) (ap pr₁ (𝓤.idtoeqv-β' e)) (ℍ A (λ B p → isequiv (coe p ∘_)) (qinv-to-isequiv (qinv-𝑖𝑑 _)) B (𝓤.ua e)) where module 𝓤 = is-univalent isuniv {A} {B}

→-preserves-dom-≃' : is-univalent 𝓤 → {A B : 𝓤 ̇} (X : 𝓥 ̇) (e : A ≃ B) → isequiv {_} {_} {B → X} {A → X} (_∘ pr₁ e) 
→-preserves-dom-≃' isuniv {A} {B} X e = transport (λ - → isequiv (_∘ -)) (ap pr₁ (𝓥.idtoeqv-β' e)) (ℍ A (λ B p → isequiv (_∘ coe p)) (qinv-to-isequiv (qinv-𝑖𝑑 _)) B (𝓥.ua e)) where module 𝓥 = is-univalent isuniv {A} {B}


-- Corollary 4.9.3.

module corollary-4-9-3 (isuniv : is-univalent 𝓤) {A : 𝓤 ̇} {P : A → 𝓤 ̇} (P-is-Contr : Π (isContr ∘ P)) where

  post-∘-with-pr₁-is-equiv : isequiv {_} {_} {A → Σ P} {A → A} (pr₁ ∘_)
  post-∘-with-pr₁-is-equiv = →-preserves-codom-≃' isuniv A (Σ-of-Contr-family-is-base A P P-is-Contr)

  post-∘-with-pr₁-is-ContrMap : isContrMap {_} {_} {A → Σ P} {A → A} (pr₁ ∘_)
  post-∘-with-pr₁-is-ContrMap = ishae-to-isContrMap _ post-∘-with-pr₁-is-equiv

  δ : A → Σ P -- diagonal map
  δ x = let y : P x
            y = pr₁ (P-is-Contr x)
        in x , y

  pre-∘-with-diagonal-is-equiv : isequiv {_} {_} {Σ P → A} {A → A} (_∘ δ)
  pre-∘-with-diagonal-is-equiv = →-preserves-dom-≃' isuniv A (≃-sym (Σ-of-Contr-family-is-base A P P-is-Contr))

open corollary-4-9-3 public hiding (δ)


-- Test

module test (isuniv : is-univalent (𝓤 ⊔ 𝓥)) {A : 𝓤 ̇} {P : A → 𝓥 ̇} (P-is-Contr : Π (isContr ∘ P)) where

  post-∘-with-pr₁-is-equiv'' : isequiv {_} {_} {A → Σ P} {A → Lift 𝓥 A} ((lift ∘ pr₁) ∘_)
  post-∘-with-pr₁-is-equiv'' = →-preserves-codom-≃' {𝓤 ⊔ 𝓥} {𝓤} isuniv A {Σ P} {Lift 𝓥 A} (Σ-of-Contr-family-is-base A P P-is-Contr ● lift , (qinv-to-isequiv (lower , ((hrefl _) , (hrefl _)))))

  post-∘-with-pr₁-is-ContrMap'' : isContrMap {_} {_} {A → Σ P} {A → Lift 𝓥 A} ((lift ∘ pr₁) ∘_)
  post-∘-with-pr₁-is-ContrMap'' = ishae-to-isContrMap _ post-∘-with-pr₁-is-equiv''

   
--


module bootstrapping where

  {- This module generalizes the previous lemmas to be able obtain inter-universal function extensionality. The proof of the book works within a universe and would only let us obtain intra-universal function extensionality because we don't have strict cumulativity of universes. -}

  -- Univalence implies non-dependent function extensionality

  univalence-to-non-dep-funext : is-univalent 𝓥 → non-dep-funext 𝓤 𝓥
  univalence-to-non-dep-funext {𝓥} {𝓤} isuniv {A} {B} {f} {g} h = ap (_∘ (λ x → f x , g x , h x)) q where

    -- Type family for dual of corollary 4.9.3

    P : B → 𝓥 ̇
    P x = Σ y ꞉ B , x ≡ y

    -- Instantiation of dual of corollary 4.9.3

    open module M = corollary-4-9-3 isuniv {B} {P} (free-right-endpt-is-Contr B) using (δ) renaming (pre-∘-with-diagonal-is-equiv to α-is-equiv)

    α : (Σ P → B) → (B → B)
    α = _∘ δ
    α⁻¹ = isequiv₁ α-is-equiv
    η = isequiv₂ α-is-equiv
    ε = isequiv₃ α-is-equiv

    -- Application of equivalence to obtain path

    π₁ : Σ P → B
    π₁ (x , y , p) = x
    π₂ : Σ P → B
    π₂ (x , y , p) = y
    q : π₁ ≡ π₂
    q = η π₁ ⁻¹ ∙ ap α⁻¹ (refl _) ∙ η π₂


  -- Boostrapping:

  -- 1. Corollary 4.9.2 generalized

  →-preserves-codom-≃'' : is-univalent 𝓥 → is-univalent 𝓦 → (X : 𝓤 ̇) {A : 𝓥 ̇} {B : 𝓦 ̇} (e : A ≃ B) → isequiv {_} {_} {X → A} {X → B} (pr₁ e ∘_)  
  →-preserves-codom-≃'' {𝓥} {𝓦} {𝓤} 𝓥-is-univ 𝓦-is-univ X (f , g , η , ε , τ) = qinv-to-isequiv (
    (g ∘_) ,
    (λ h → funext₂ (ε ∘ h)) ,
    λ h → funext₁ (η ∘ h)
    )
    where
    funext₁ : non-dep-funext 𝓤 𝓥
    funext₁ = univalence-to-non-dep-funext 𝓥-is-univ
    funext₂ : non-dep-funext 𝓤 𝓦
    funext₂ = univalence-to-non-dep-funext 𝓦-is-univ

  →-preserves-dom-≃'' : is-univalent 𝓦 → {A : 𝓤 ̇} {B : 𝓥 ̇} (X : 𝓦 ̇) (e : A ≃ B) → isequiv {_} {_} {B → X} {A → X} (_∘ pr₁ e)  
  →-preserves-dom-≃'' {𝓦} {𝓤} {𝓥} 𝓦-is-univ X (f , g , η , ε , τ) =
    let funext' : (𝓤 : Universe) → non-dep-funext 𝓤 𝓦
        funext' 𝓤 = univalence-to-non-dep-funext 𝓦-is-univ
    in qinv-to-isequiv (
    _∘ g ,
    (λ h → funext' 𝓤 (λ x → ap h (η x))) ,
    λ h → funext' 𝓥 (λ x → ap h (ε x))
    )

  -- 2. Corollary 4.9.3 generalized

  module corollary-4-9-3' {𝓤 𝓥 : Universe} (isuniv₁ : is-univalent 𝓤) (isuniv₂ : is-univalent (𝓤 ⊔ 𝓥)) {A : 𝓤 ̇} {P : A → 𝓥 ̇} (P-is-Contr : Π (isContr ∘ P)) where

    post-∘-with-pr₁-is-equiv' : isequiv {_} {_} {A → Σ P} {A → A} (pr₁ ∘_)
    post-∘-with-pr₁-is-equiv' = →-preserves-codom-≃'' {𝓤 ⊔ 𝓥} {𝓤} {𝓤} isuniv₂ isuniv₁ A {Σ P} {A} (Σ-of-Contr-family-is-base A P P-is-Contr)

    post-∘-with-pr₁-is-ContrMap' : isContrMap {_} {_} {A → Σ P} {A → A} (pr₁ ∘_)
    post-∘-with-pr₁-is-ContrMap' = ishae-to-isContrMap _ post-∘-with-pr₁-is-equiv'

    -- Dual version of the corollary:

    δ : A → Σ P -- diagonal map
    δ x = let y : P x
              y = pr₁ (P-is-Contr x)
          in x , y

    pre-∘-with-diagonal-is-equiv' : isequiv {_} {_} {Σ P → A} {A → A} (_∘ δ)
    pre-∘-with-diagonal-is-equiv' = →-preserves-dom-≃'' isuniv₁ A (≃-sym (Σ-of-Contr-family-is-base A P P-is-Contr))

  open corollary-4-9-3' public hiding (δ)

open bootstrapping public


-- Theorem 4.9.4 (Univalence implies weak function extensionality)

univalence-to-weak-funext : {𝓤 𝓥 : Universe} → is-univalent 𝓤 → is-univalent (𝓤 ⊔ 𝓥) → {A : 𝓤 ̇} (P : A → 𝓥 ̇) → weak-funext P  
univalence-to-weak-funext {𝓤} {𝓥} isuniv₁ isuniv₂ {A} P P-is-Contr = retract-of-Contr-is-Contr (ψ , (ϕ , (hrefl _))) (α-is-ContrMap id)
  where
  α : (A → Σ P) → (A → A) 
  α = pr₁ ∘_
  α-is-ContrMap : isContrMap α
  α-is-ContrMap = post-∘-with-pr₁-is-ContrMap' {𝓤} {𝓥} isuniv₁ isuniv₂ P-is-Contr 
  ϕ : Π P → fib α id
  ϕ f = (λ x → x , f x) , (refl _)
  ψ : fib α id → Π P
  ψ (g , p) x = transport P (happly p x) (pr₂ (g x))


univalence-to-weak-funext' : {𝓤 𝓥 : Universe} → is-univalent (𝓤 ⊔ 𝓥) → {A : 𝓤 ̇} (P : A → 𝓥 ̇) → weak-funext P  
univalence-to-weak-funext' {𝓤} {𝓥} isuniv {A} P P-is-Contr = retract-of-Contr-is-Contr (ψ , ϕ , hrefl _) (α-is-ContrMap lift)
  where
  α : (A → Σ P) → (A → Lift 𝓥 A)
  α = (lift ∘ pr₁) ∘_
  α-is-ContrMap : isContrMap α
  α-is-ContrMap = test.post-∘-with-pr₁-is-ContrMap'' {𝓤} {𝓥} isuniv P-is-Contr 
  ϕ : Π P → fib α lift
  ϕ f = (λ x → x , f x) , (refl _)
  ψ : fib α lift → Π P
  ψ (g , p) x = transport P (ap lower (happly p x)) (pr₂ (g x))



-- Theorem 4.9.5. (Weak function extensionality implies function extensionality)

weak-funext-to-funext : {A : 𝓤 ̇} {P : A → 𝓥 ̇} {f g : Π P} → isequiv (happly {𝓤} {𝓥} {A} {P} {f} {g})
weak-funext-to-funext = {!!}

{-# OPTIONS --without-K --exact-split --safe #-}

open import Ch1.Type-theory
open import Ch2.Homotopy-type-theory
open import Ch3.Sets-and-logic
open import Ch4.2-Half-adjoint-equivalences
open import Ch4.4-Contractible-fibers
open import Ch4.7-Closure-properties-of-equivalences
module Ch4.9-Univalence-implies-funext where


-- Definition 4.9.1 (The Weak Function Extensionality Principle).

weak-funext : (𝓤 𝓥 : Universe) → (𝓤 ⊔ 𝓥) ⁺ ̇ 
weak-funext 𝓤 𝓥 = {A : 𝓤 ̇} {P : A → 𝓥 ̇} → Π (isContr ∘ P) → isContr (Π P) 

-- Lemma 4.9.2 (For a proof using function extensionality, see lemma 4.2.8 and exercise 2.17).

→-preserves-codom-≃' : (𝓥 : Universe) → is-univalent 𝓥 → (X : 𝓤 ̇) {A B : 𝓥 ̇} (e : A ≃ B) → isequiv {_} {_} {X → A} {X → B} (pr₁ e ∘_)
→-preserves-codom-≃' 𝓥 isuniv X {A} {B} e = transport (λ - → isequiv (- ∘_)) (ap pr₁ (𝓤.idtoeqv-β' e)) (ℍ A (λ B p → isequiv (coe p ∘_)) (qinv-to-isequiv (qinv-𝑖𝑑 _)) B (𝓤.ua e)) where module 𝓤 = is-univalent isuniv {A} {B}

→-preserves-dom-≃' : is-univalent 𝓤 → {A B : 𝓤 ̇} (X : 𝓥 ̇) (e : A ≃ B) → isequiv {_} {_} {B → X} {A → X} (_∘ pr₁ e) 
→-preserves-dom-≃' isuniv {A} {B} X e = transport (λ - → isequiv (_∘ -)) (ap pr₁ (𝓥.idtoeqv-β' e)) (ℍ A (λ B p → isequiv (_∘ coe p)) (qinv-to-isequiv (qinv-𝑖𝑑 _)) B (𝓥.ua e)) where module 𝓥 = is-univalent isuniv {A} {B}


-- Corollary 4.9.3.

module corollary-4-9-3 (𝓤 𝓥 : Universe) (isuniv : is-univalent (𝓤 ⊔ 𝓥)) {A : 𝓤 ̇} {P : A → 𝓥 ̇} (P-is-Contr : Π (isContr ∘ P)) where

  post-∘-with-pr₁-is-equiv'' : isequiv {_} {_} {A → Σ P} {A → Lift 𝓥 A} ((lift ∘ pr₁) ∘_)
  post-∘-with-pr₁-is-equiv'' =  →-preserves-codom-≃' (𝓤 ⊔ 𝓥) isuniv A {Σ P} {Lift 𝓥 A} (Σ-of-Contr-family-is-base A P P-is-Contr ● lift , (qinv-to-isequiv (lower , ((hrefl _) , (hrefl _)))))

  post-∘-with-pr₁-is-ContrMap'' : isContrMap {_} {_} {A → Σ P} {A → Lift 𝓥 A} ((lift ∘ pr₁) ∘_)
  post-∘-with-pr₁-is-ContrMap'' = ishae-to-isContrMap _ post-∘-with-pr₁-is-equiv''

open corollary-4-9-3 public


-- Theorem 4.9.4 (Univalence implies weak function extensionality)

univalence-to-weak-funext : (𝓤 𝓥 : Universe) → is-univalent (𝓤 ⊔ 𝓥) → weak-funext 𝓤 𝓥
univalence-to-weak-funext 𝓤 𝓥 isuniv {A} {P} P-is-Contr = retract-of-Contr-is-Contr (ψ , ϕ , hrefl _) (α-is-ContrMap lift)
  where
  α : (A → Σ P) → (A → Lift 𝓥 A)
  α = (lift ∘ pr₁) ∘_
  α-is-ContrMap : isContrMap α
  α-is-ContrMap = post-∘-with-pr₁-is-ContrMap'' 𝓤 𝓥 isuniv P-is-Contr 
  ϕ : Π P → fib α lift
  ϕ f = (λ x → x , f x) , (refl _)
  ψ : fib α lift → Π P
  ψ (g , p) x = transport P (ap lower (happly p x)) (pr₂ (g x))


-- Theorem 4.9.5. (Weak function extensionality implies function extensionality)

weak-funext-to-funext : (𝓤 𝓥 : Universe) → weak-funext 𝓤 𝓥 → hfunext 𝓤 𝓥

-- First, we show the retract version of theorem 2.15.7:

dep-Σ-UMP' : (X : 𝓤 ̇) (A : X → 𝓥 ̇) (P : (x : X) → A x → 𝓦 ̇) → (Σ g ꞉ Π A , ((x : X) → P x (g x))) ◁ ((x : X) → Σ (P x))
dep-Σ-UMP' X A P =
  (λ f → (λ x → pr₁ (f x)) , (λ x → pr₂ (f x))) ,
  Σ-induction (λ g h x → g x , h x) ,
  hrefl _

-- Second, we prove theorem 4.9.5:

weak-funext-to-funext 𝓤 𝓥 wfe {A} {P} {f} {g} = fourth g where
  first : (Σ g ꞉ Π P , f ∼ g) ◁ ((x : A) → Σ u ꞉ P x , f x ≡ u)
  first = dep-Σ-UMP' A P (λ x u → f x ≡ u)
  second : isContr (Σ g ꞉ Π P , f ∼ g)
  second = retract-of-Contr-is-Contr first (wfe (λ x → free-right-endpt-is-Contr (P x) (f x)))
  tot-happly : (Σ g ꞉ Π P , f ≡ g) → Σ g ꞉ Π P , f ∼ g
  tot-happly = total (λ g  → happly {𝓤} {𝓥} {A} {P} {f} {g})
  third : isequiv (tot-happly)
  third = map-between-Contrs-is-equiv tot-happly (free-right-endpt-is-Contr _ f) second
  fourth : (g : Π P) → ishae (happly {𝓤} {𝓥} {A} {P} {f} {g})
  fourth = pr₂ (fiberwise-≃-iff-total-≃.Hae (λ g → happly {𝓤} {𝓥} {A} {P} {f} {g})) third 


-- Global univalence implies golbal function extensionality

module Full-Univalence (univ : Univalence) where

  open Basic-Univalence univ public

  abstract
    instance
      fe : FunExt
      fe {𝓤} {𝓥} = weak-funext-to-funext 𝓤 𝓥 (univalence-to-weak-funext 𝓤 𝓥 (idtoeqv-is-equiv {𝓤 ⊔ 𝓥}))

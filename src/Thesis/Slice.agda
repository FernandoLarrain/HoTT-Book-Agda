{-# OPTIONS --without-K --exact-split --safe #-}

open import Ch1.Type-theory
open import Ch2.Homotopy-type-theory
open import Ch3.Sets-and-logic
open import Ch4.Equivalences
open import Ch5.Exercises
open import Thesis.Z-Algebras
open import Thesis.Identity-types

module Thesis.Slice where


-- XI. Slice over an algebra.

Slice : (𝓥 : Universe) → Alg 𝓤 → 𝓤 ⊔ (𝓥 ⁺) ̇
Slice {𝓤} 𝓥 A = Σ B ꞉ Alg 𝓥 , Hom B A

module Slice-is-FibAlg (univ : Univalence) where

  open Full-Univalence univ

  Slice-is-FibAlg : (A : Alg 𝓤) → Slice 𝓤 A ≃ FibAlg 𝓤 A
  Slice-is-FibAlg {𝓤} (A , a₀ , s , i) =
    Slice 𝓤 A'
      ≃⟨ lemma1 ⟩
    Slice'
      ≃⟨ Σ-preserves-≃' _ _ (χ , χ-is-equiv) (λ E → ×-preserves-≃ (fibs-of-pr₁-are-values a₀) (lemma2 (s , i) E E))  ⟩
    FibAlg 𝓤 A' ■

    where

    open thm-4-8-3 univ A using (χ ; χ-is-equiv)

    A' = (A , a₀ , s , i)

    Slice' = (Σ w ꞉ (Σ λ B → B → A) , fib (pr₂ w) a₀ × (Σ s' ꞉ pr₁ w ≃ pr₁ w , pr₂ w ∘ pr₁ s' ∼ s ∘ pr₂ w))

    lemma1 : Slice 𝓤 A' ≃ Slice'
    lemma1 = ϕ , qinv-to-isequiv (ψ , hrefl _ , hrefl _) 
      where
      ϕ : Slice 𝓤 A' → Slice'
      ϕ ((B , b₀ , s') , (f , f₀ , f-s)) = ((B , f) , ((b₀ , f₀) , (s' , f-s)))
      ψ : Slice' → Slice 𝓤 A'
      ψ ((B , f) , ((b₀ , f₀) , (s' , f-s))) = ((B , b₀ , s') , (f , f₀ , f-s))

    lemma2 : {A₁ A₂ : 𝓤 ̇} (s : A₁ ≃ A₂) (E₁ : A₁ → 𝓤 ̇) (E₂ : A₂ → 𝓤 ̇) → (Σ s' ꞉ (Σ E₁ ≃ Σ E₂) , pr₁ ∘ pr₁ s' ∼ pr₁ s ∘ pr₁) ≃ (Σ t ꞉ ((a : A₁) → E₁ a → E₂ ((pr₁ s) a)) , ((a : A₁) → isequiv (t a)))
    lemma2 s E₁ E₂ = ≃-sym (Σ-assoc _ _ _) ●
      (Σ-preserves-family-≃ (λ s' → ×-swap _ _) ●
        (Σ-assoc _ _ _ ●
          Σ-preserves-≃' _ _ (families-of-funs↓.equiv (pr₁ s) E₁ E₂)
          (λ g → ≃-sym
            (⇔-to-≃ (Π-preserves-Props _ λ a → ishae-is-Prop _) (ishae-is-Prop _)            (fiberwise-≃-iff-total↓-≃ (pr₁ s) E₁ E₂ (pr₂ s) g)))))

  -- Equivalence gives TotAlg and π₁.

  equiv-gives-TotAlg : (A : Alg 𝓤) → pr₁ ∘ (inv (Slice-is-FibAlg A)) ∼ TotAlg A
  equiv-gives-TotAlg A E = dpair-≡ (refl _ , pair-≡ (refl _ , dpair-≡ (refl _ , ishae-is-Prop _ _ _))) 

  equiv-gives-π₁ : (A : Alg 𝓤) → pr₂ ∘ (inv (Slice-is-FibAlg A)) ∼ π₁ A
  equiv-gives-π₁ A E = refl _


-- XII. Algebra Sections are Sections.

AlgSec-is-Sec : ⦃ fe : FunExt ⦄ (A : Alg 𝓤) (E : FibAlg 𝓤 A) → AlgSec A E ≃ (Σ f ꞉ (Hom A (TotAlg A E)) , comp A (TotAlg A E) A (π₁ A E) f ≡ algid A)
AlgSec-is-Sec {𝓤} (A , a₀ , s , i) (E , e₀ , s' , j) = ≃-sym (
  Sec₀
    ≃⟨ lemma1 ⟩
  Sec₁
    ≃⟨ lemma2 ⟩
  Sec₂
    ≃⟨ lemma3 ⟩
  Sec₃
    ≃⟨ ≃-sym (Σ-preserves-≃ _ _ (dfuns-are-sections.equiv E) (λ f → ×-preserves-≃ (lemma4 f) (lemma5 f))) ⟩
  AlgSec A' E' ■)

  where

  A' : Alg 𝓤
  A' = (A , a₀ , s , i)

  E' : FibAlg 𝓤 A'
  E' = (E , e₀ , s' , j)

  Sec₀ Sec₁ Sec₂ Sec₃ : 𝓤 ̇

  Sec₀ = (Σ f ꞉ (Hom A' (TotAlg A' E')) , comp A' (TotAlg A' E') A' (π₁ A' E') f ≡ algid A')

  Sec₁ = (Σ f ꞉ (Hom A' (TotAlg A' E')) , HomId A' A' (comp A' (TotAlg A' E') A' (π₁ A' E') f) (algid A'))

  Sec₂ = (Σ w ꞉ (Σ f ꞉ (A → Σ E), pr₁ ∘ f ∼ id) , (Σ f₀ ꞉ (pr₁ w) a₀ ≡ (a₀ , e₀) , pr₂ w a₀ ≡ ap pr₁ f₀ ∙ refl a₀ ∙ refl a₀) × (Σ f-s ꞉ ((a : A) → pr₁ w (s a) ≡ (s (pr₁ (pr₁ w a)) , s' (pr₁ (pr₁ w a)) (pr₂ (pr₁ w a)))) , ((a : A) → pr₂ w (s a) ≡ ap pr₁ (f-s a) ∙ refl (s (pr₁ ((pr₁ w) a))) ∙ ap s (pr₂ w a) ∙ refl (s a))))

  Sec₃ = (Σ w ꞉ (Σ f ꞉ (A → Σ E), pr₁ ∘ f ∼ id) , (Σ f₀ ꞉ (pr₁ w) a₀ ≡ (a₀ , e₀) , pr₂ w a₀ ≡ ap pr₁ f₀) × (Σ f-s ꞉ ((a : A) → pr₁ w (s a) ≡ (s (pr₁ (pr₁ w a)) , s' (pr₁ (pr₁ w a)) (pr₂ (pr₁ w a)))) , ((a : A) → pr₂ w (s a) ≡ ap pr₁ (f-s a) ∙ ap s (pr₂ w a))))

  lemma1 : Sec₀ ≃ Sec₁
  lemma1 = Σ-preserves-family-≃ (λ f → IdHom-≃-HomId A' A' _ _)

  lemma2 : Sec₁ ≃ Sec₂
  lemma2 = ϕ , qinv-to-isequiv (ψ , hrefl _ , hrefl _)
    where
    ϕ : Sec₁ → Sec₂
    ϕ ((f , f₀ , f-s) , (p , p₀ , p-s)) = (f , p) , (f₀ , p₀) , (f-s , p-s)
    ψ : Sec₂ → Sec₁
    ψ ((f , p) , (f₀ , p₀) , (f-s , p-s)) = (f , f₀ , f-s) , (p , p₀ , p-s)

  lemma3 : Sec₂ ≃ Sec₃
  lemma3 = Σ-preserves-family-≃ (λ w → ×-preserves-≃ (Σ-preserves-family-≃ (λ w₀ → post-∙-≃ _ ((ru _ ∙ ru _) ⁻¹))) (Σ-preserves-family-≃ (λ w-s → Π-preserves-family-≃ (λ a → post-∙-≃ _ (((ru _ ∙ᵣ ap s (pr₂ w a)) ∙ ru _) ⁻¹))))) 

  lemma4 : (g : Π E) → (g a₀ ≡ e₀) ≃ (Σ f₀ ꞉ Id (Σ E) (a₀ , g a₀) (a₀ , e₀) , refl a₀ ≡ ap pr₁ f₀)
  lemma4 g =
    _
      ≃⟨ ≃-sym (Σ-over-Contr-base-is-fib _ _ (free-right-endpt-is-Contr _ _)) ⟩
    _
     ≃⟨ ≃-sym (Σ-assoc _ _ _) ⟩
    _
     ≃⟨ Σ-preserves-family-≃ (λ p → ×-swap _ _) ⟩
    _
     ≃⟨ Σ-assoc _ _ _ ⟩
    (Σ f₀ ꞉ (Σ p ꞉ a₀ ≡ a₀ , transport E p (g a₀) ≡ e₀) , refl a₀ ≡ pr₁ f₀)
     ≃⟨ Σ-preserves-≃ _ _ (≃-sym Σ-≡-≃) (Σ-induction (λ p q → post-∙-≃ _ ((dpr₁-≡-β _ q) ⁻¹))) ⟩
    _ ■

  lemma5 : (g : Π E) → ((a : A) → g (s a) ≡ s' a (g a)) ≃ (Σ f-s ꞉ ((a : A) → (s a , g (s a)) ≡ (s a , s' a (g a))) , ((a : A) → refl (s a) ≡ ap pr₁ (f-s a) ∙ refl (s a)))
  lemma5 g =
    _
      ≃⟨ Π-preserves-family-≃ (λ a →
      _
        ≃⟨ ≃-sym (Σ-over-Contr-base-is-fib _ _ (free-right-endpt-is-Contr _ _)) ⟩
      _
        ≃⟨ ≃-sym (Σ-assoc _ _ _) ⟩
      _
        ≃⟨ Σ-preserves-family-≃ (λ p → ×-swap _ _) ⟩
      _
        ≃⟨ Σ-assoc _ _ _ ⟩
     (Σ f-sa ꞉ (Σ p ꞉ s a ≡ s a , transport E p (g (s a)) ≡ s' a (g a)) , refl (s a) ≡ pr₁ f-sa)
        ≃⟨ Σ-preserves-≃ _ _ (≃-sym Σ-≡-≃) (Σ-induction (λ p q → post-∙-≃ _ (dpr₁-≡-β _ q ⁻¹ ∙ ru _))) ⟩
      _ ■
      ) ⟩
    ((a : A) → Σ f-sa ꞉ (s a , g (s a)) ≡ (s a , s' a (g a)) , refl (s a) ≡ ap pr₁ f-sa ∙ refl (s a))
      ≃⟨ _ , (dep-Σ-UMP _ _ _) ⟩
    _ ■


-- XIV. Alternative proof of isind-≃-ishinit.

module _ (univ : Univalence) (𝓤 : Universe) where

  open Full-Univalence univ
  open Slice-is-FibAlg univ
  open import Thesis.Inductive-Z-Algebras
  open import Thesis.Hinitial-Z-Algebras
  open import Thesis.ZAlg-is-Cofiltered
  open import Thesis.WildCats
    (𝓤 ⁺)
    𝓤
    (Alg 𝓤)
    Hom (λ {A} {B} {C} → comp A B C)
    algid
    (λ {A} {B} {C} {D} h g f → associator A B C D f g h)
    (λ {A} {B} → right-unitor A B)
    (λ {A} {B} → left-unitor A B)
    _⨂_
    (λ {A} {B} → proj₁ A B)
    (λ {A} {B} → proj₂ A B)
    (λ {A} {B} → Eqz A B)
    (λ {A} {B} → Eqz-map A B)
    (λ {A} {B} → Eqz-equalizes A B) using (ishinit-≃-isind)

  isind-≃-ishinit' : (A : Alg 𝓤) → isind 𝓤 A ≃ ishinit 𝓤 A
  isind-≃-ishinit' A =
    _
      ≃⟨ Π-preserves-≃ _ _ (≃-sym (Slice-is-FibAlg A)) (λ E → AlgSec-is-Sec A E) ⟩
    _
      ≃⟨ GCCAdj _ _ _ ⟩
    _
      ≃⟨ ≃-sym (ishinit-≃-isind A) ⟩
    _ ■

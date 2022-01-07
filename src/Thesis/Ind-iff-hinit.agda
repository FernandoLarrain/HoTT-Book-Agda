{-# OPTIONS --without-K --exact-split --safe #-}

open import Ch1.Type-theory
open import Ch2.Homotopy-type-theory
open import Ch3.Sets-and-logic
open import Ch4.Equivalences
open import Thesis.Z-Algebras
open import Thesis.Identity-types
open import Thesis.Hinitial-Z-Algebras
open import Thesis.Inductive-Z-Algebras

module Thesis.Ind-iff-hinit where


-- I. Every Inductive Algebra is Homotopy-Initial

isind-to-hasrec : (A : Alg 𝓤) → isind 𝓤 A → hasrec 𝓤 A
isind-to-hasrec A A-ind B = A-ind (ConstFibAlg A B)

isind-to-hasrecunique : ⦃ fe : FunExt ⦄ (A : Alg 𝓤) → isind 𝓤 A → hasrecunique 𝓤 A
isind-to-hasrecunique {𝓤} A A-ind B = uniqueness-pple A A-ind (ConstFibAlg A B)

isind-to-ishinit : ⦃ fe : FunExt ⦄ (A : Alg 𝓤) → isind 𝓤 A → ishinit 𝓤 A
isind-to-ishinit A A-ind B = pr₂ isContr-iff-is-inhabited-Prop (isind-to-hasrec A A-ind B , isind-to-hasrecunique A A-ind B)


-- II. Every Initial Algebra is Inductive

ishinit-to-isind : ⦃ fe : FunExt ⦄ (A : Alg 𝓤) → ishinit 𝓤 A → isind 𝓤 A
ishinit-to-isind {𝓤} (A , a₀ , s , i) init (E , e₀ , s' , j) = g , g₀ , g-s

  where

  -- 1. Useful names

  A' : Alg 𝓤
  A' = (A , a₀ , s , i)

  E' : FibAlg 𝓤 A'
  E' = (E , e₀ , s' , j)

  T : Alg 𝓤
  T = TotAlg A' E'

  -- 2. Initiality gives morphism f into T

  A-rec : Hom A' T
  A-rec = pr₁ (init T)

  f : A → Σ E
  f = pr₁ A-rec

  f₀ : f a₀ ≡ (a₀ , e₀)
  f₀ = pr₁ (pr₂ A-rec)

  f-s : f ∘ s ∼ total↓ E s s' ∘ f
  f-s = pr₂ (pr₂ A-rec)

  -- 2.1 First components of f

  f₁ : A → A
  f₁ = pr₁ ∘ f

  f₀₁ : f₁ a₀ ≡ a₀
  f₀₁ = pr₁ (dpr-≡ f₀)

  f-s₁ : f₁ ∘ s ∼ s ∘ f₁
  f-s₁ a = pr₁ (dpr-≡ (f-s a))

  -- 2.2 Second components of f

  f₂ : (a : A) → E (f₁ a)
  f₂ = pr₂ ∘ f

  f₀₂ : transport E f₀₁ (f₂ a₀) ≡ e₀
  f₀₂ = pr₂ (dpr-≡ f₀)

  f-s₂ : (a : A) → transport E (f-s₁ a) (f₂ (s a)) ≡ s' (f₁ a) (f₂ a)
  f-s₂ a = pr₂ (dpr-≡ (f-s a))


  -- 4. Initiality gives path from π₁∘f to algid A'

  A-uniqueness : isProp (Hom A' A')
  A-uniqueness = pr₂ (pr₁ isContr-iff-is-inhabited-Prop (init A'))    

  path : Id (Hom A' A') (f₁ , f₀₁ , f-s₁) (algid A')
  path = A-uniqueness _ _

  -- 4.1 Extension of path

  pathext : HomId A' A' (f₁ , f₀₁ , f-s₁) (algid A')
  pathext = Hom-≡-elim A' A' _ _ path

  H : f₁ ∼ id
  H = pr₁ pathext

  H₀ : H a₀ ≡ f₀₁
  H₀ = pr₁ (pr₂ pathext) ∙ ru _ ⁻¹  

  H-s : (a : A) → H (s a) ≡ f-s₁ a ∙ ap s (H a)
  H-s a = pr₂ (pr₂ pathext) a ∙ ru _ ⁻¹

  -- 5. Construction of section

  g : (a : A) → E a
  g a = transport E (H a) (f₂ a)

  g₀ : g a₀ ≡ e₀
  g₀ = transport E (H a₀) (f₂ a₀)
           ≡⟨ ap (λ - → transport E - (f₂ a₀)) H₀ ⟩
         transport E f₀₁ (f₂ a₀)
           ≡⟨ f₀₂ ⟩
         e₀ ∎

  g-s : (a : A) → g (s a) ≡ s' a (g a)
  g-s a = transport E (H (s a)) (f₂ (s a))
            ≡⟨ ap (λ - → transport E - (f₂ (s a))) (H-s a) ⟩
          transport E (f-s₁ a ∙ ap s (H a)) (f₂ (s a))
            ≡⟨ transport-∙ E (f-s₁ a) (ap s (H a)) (f₂ (s a)) ⁻¹ ⟩
          transport E (ap s (H a)) (transport E (f-s₁ a) (f₂ (s a)))
            ≡⟨ ap (transport E (ap s (H a))) (f-s₂ a) ⟩
          transport E (ap s (H a)) (s' (f₁ a) (f₂ a))
            ≡⟨ ℍ (f₁ a) (λ b p → transport E (ap s p) (s' (f₁ a) (f₂ a)) ≡ s' b (transport E p (f₂ a))) (refl _) a (H a) ⟩
          s' a (transport E (H a) (f₂ a)) ∎


-- III. The Equivalence

isind-iff-ishinit : ⦃ fe : FunExt ⦄ (A : Alg 𝓤) → isind 𝓤 A ⇔ ishinit 𝓤 A
isind-iff-ishinit A = (isind-to-ishinit A) , (ishinit-to-isind A)

isind-≃-ishinit : ⦃ fe : FunExt ⦄ (A : Alg 𝓤) → isind 𝓤 A ≃ ishinit 𝓤 A
isind-≃-ishinit {𝓤} A = ⇔-to-≃ (isind-is-Prop A) (ishinit-is-Prop 𝓤 A) (isind-iff-ishinit A)


-- III. There Is Only One Notion of Inductive ℤ-Algebra.

module _  ⦃ fe : FunExt ⦄ (𝓤 : Universe) where

  open import Thesis.Cofiltered
  open import Thesis.Naive-cats
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
    (λ {A} {B} → Eqz-equalizes A B)
    renaming (isind to isind' ; ishinit-≃-isind to ishinit-≃-isind')

  isind-≃-isind' : (A : Alg 𝓤) → isind 𝓤 A ≃ isind' A
  isind-≃-isind' A = isind-≃-ishinit A ● ishinit-≃-isind' A

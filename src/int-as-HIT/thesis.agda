{-# OPTIONS --without-K --exact-split #-}

open import Ch1.Type-theory
open import Ch2.Homotopy-type-theory
open import Ch3.Sets-and-logic
open import Ch4.Equivalences
open import Ch5.8-Id-types-and-id-systems

module int-as-HIT.thesis where

postulate
  instance
    fe : FunExt
    univ : Univalence

-- I. The (Wild) Category of ℤ-Algebras

module ℤ-Algebras where

  -- Objects

  AlgStr : 𝓤 ̇ → 𝓤 ̇
  AlgStr A = A × (Σ s ꞉ (A → A) , ishae s)
  
  Alg : (𝓤 : Universe) → 𝓤 ⁺ ̇
  Alg 𝓤 = Σ A ꞉ (𝓤 ̇) , AlgStr A

  -- Morphisms

  HomStr : (A : Alg 𝓤) (B : Alg 𝓥) → (pr₁ A → pr₁ B) → 𝓤 ⊔ 𝓥 ̇
  HomStr (A , a₀ , s , i) (B , b₀ , t , j) f = (f a₀ ≡ b₀) × (f ∘ s ∼ t ∘ f)
  
  Hom : Alg 𝓤 → Alg 𝓥 → 𝓤 ⊔ 𝓥 ̇
  Hom A B = Σ f ꞉ (pr₁ A → pr₁ B) , HomStr A B f 

  -- Composition

  comp : (A : Alg 𝓤) (B : Alg 𝓥) (C : Alg 𝓦) → Hom B C → Hom A B → Hom A C
  comp A B C (g , g₀ , g-s) (f , f₀ , f-β) = g ∘ f , (ap g f₀ ∙ g₀) , λ a → ap g (f-β a) ∙ g-s (f a)

  -- Identity

  algid : (A : Alg 𝓤) → Hom A A
  algid A = id , refl _ , hrefl _

open ℤ-Algebras public


-- II. The Identity Type of Morphisms

module Morphism-Id (A' : Alg 𝓤) (B' : Alg 𝓥) where

  A : 𝓤 ̇
  A = pr₁ A'
  a₀ : A
  a₀ = pr₁ (pr₂ A')
  s : A → A
  s = pr₁ (pr₂ (pr₂ A'))

  B : 𝓥 ̇
  B = pr₁ B'
  b₀ : B
  b₀ = pr₁ (pr₂ B')
  t : B → B
  t = pr₁ (pr₂ (pr₂ B'))
  
  -- Extension of identity type of morphisms

  HomId : Hom A' B' → Hom A' B' → 𝓤 ⊔ 𝓥 ̇
  HomId (f , f₀ , f-s) (g , g₀ , g-s) = Σ H ꞉ (f ∼ g) , (H a₀ ⁻¹ ∙ f₀ ≡ g₀) × ((a : A) → f-s a ∙ ap t (H a) ≡ H (s a) ∙ g-s a)

  -- From path to extension

  Hom-≡-elim : (f' g' : Hom A' B') → f' ≡ g' → HomId f' g'
  Hom-≡-elim f' .f' (refl .f') = hrefl _ , (lu _ ⁻¹) , λ a → ru _ ⁻¹ ∙ lu _

  -- The total space of HomId f' is contractible

  module TotHomId-is-Contr (f : A → B) (f₀ : f a₀ ≡ b₀) (f-s : f ∘ s ∼ t ∘ f) where

    f' : Hom A' B'
    f' = (f , f₀ , f-s)

    -- Total space of HomId f'

    TotHomId : 𝓤 ⊔ 𝓥 ̇
    TotHomId = Σ g' ꞉ Hom A' B' , HomId f' g'

    -- Decomposition of total space into contractible types

    Tot-fun : 𝓤 ⊔ 𝓥 ̇
    Tot-fun = Σ g ꞉ (A → B) , f ∼ g

    Tot-fun-is-Contr : isContr (Tot-fun)
    Tot-fun-is-Contr = ≃-preserves-Contr (Σ-preserves-family-≃ (λ g → happly , happly-is-equiv)) (free-right-endpt-is-Contr _ _)

    Tot-path : Tot-fun → 𝓥 ̇
    Tot-path (g , H) = Σ g₀ ꞉ (g a₀ ≡ b₀) , H a₀ ⁻¹ ∙ f₀ ≡ g₀

    Tot-path-is-Contr : isContr (Tot-path (f , hrefl f))
    Tot-path-is-Contr = free-right-endpt-is-Contr _ _

    Tot-htpy : Tot-fun → 𝓤 ⊔ 𝓥 ̇
    Tot-htpy (g , H) = Σ g-s ꞉ (g ∘ s ∼ t ∘ g) , ((a : A) → f-s a ∙ ap t (H a) ≡ H (s a) ∙ g-s a)

    Tot-htpy-is-Contr : isContr (Tot-htpy (f , hrefl f))
    Tot-htpy-is-Contr = ≃-preserves-Contr ((split , dep-Σ-UMP A (λ a → f (s a) ≡ t (f a)) λ a x → f-s a ∙ refl (t (f a)) ≡ refl (f (s a)) ∙ x)) (Π-preserves-Contr _ λ a → ≃-preserves-Contr (Σ-preserves-family-≃ (λ x → post-∙-≃ (f-s a ∙ refl _) (lu _))) (free-right-endpt-is-Contr _ _))

    TotHomId' : 𝓤 ⊔ 𝓥 ̇
    TotHomId' = Σ w ꞉ Tot-fun , Tot-path w × Tot-htpy w

    TotHomId'-is-Contr : isContr (TotHomId')
    TotHomId'-is-Contr = ≃-preserves-Contr (≃-sym (Σ-over-Contr-base-is-fib _ _ Tot-fun-is-Contr)) (×-preserves-Contr _ _ Tot-path-is-Contr Tot-htpy-is-Contr)

    -- Correctness of decomposition

    ϕ : TotHomId → TotHomId'
    ϕ ((g , g₀ , g-s) , (H , H₀ , H-β)) = (g , H) , (g₀ , H₀) , (g-s , H-β)

    ψ : TotHomId' → TotHomId
    ψ ((g , H) , (g₀ , H₀) , (g-s , H-β)) = ((g , g₀ , g-s) , (H , H₀ , H-β))

    TotHomId-is-Contr : isContr (TotHomId)
    TotHomId-is-Contr = ≃-preserves-Contr (≃-sym (ϕ , qinv-to-isequiv (ψ , hrefl _ , hrefl _))) TotHomId'-is-Contr

  open TotHomId-is-Contr using (TotHomId-is-Contr) public

  -- Equivalence (Fundamental Theorem of Id Types)

  IdHom-≃-HomId : (f' g' : Hom A' B') → (f' ≡ g') ≃ HomId f' g' 
  IdHom-≃-HomId (f , f₀ , f-s) g' = Hom-≡-elim (f , f₀ , f-s) g' , pr₂ (fiberwise-≃-iff-total-≃.Hae (Hom-≡-elim (f , f₀ , f-s))) (map-between-Contrs-is-equiv _ (free-right-endpt-is-Contr _ _) (TotHomId-is-Contr f f₀ f-s)) g'

  -- From extension to path

  Hom-≡-intro : (f' g' : Hom A' B') → HomId f' g' → f' ≡ g'
  Hom-≡-intro f' g' = inv (IdHom-≃-HomId f' g')  

open Morphism-Id using (HomId ; Hom-≡-elim ; Hom-≡-intro) public 


-- III. Preservation of Equivalences

module Preservation-of-Equivalences (A₁ A₂ : 𝓤 ̇) (e : A₁ ≃ A₂) (B₁ B₂ : 𝓥 ̇) (e' : B₁ ≃ B₂) (f₁ : A₁ → B₁) (f₂ : A₂ → B₂) where

  s = pr₁ e
  i = pr₂ e
  p = ishae₁ i
  σ = ishae₂ i
  ρ = ishae₃ i
  τ = ishae₄ i

  s' = pr₁ e'
  i' = pr₂ e'
  p' = ishae₁ i'
  σ' = ishae₂ i'
  ρ' = ishae₃ i'
  τ' = ishae₄ i'

  s-pres : 𝓤 ⊔ 𝓥 ̇
  s-pres = f₂ ∘ s ∼ s' ∘ f₁

  p-pres : 𝓤 ⊔ 𝓥 ̇
  p-pres = f₁ ∘ p ∼ p' ∘ f₂

  module _ (α : s-pres) (β : p-pres) where

    aux-γ : f₁ ∘ p ∘ s ∼ p' ∘ s' ∘ f₁
    aux-γ a₁ = β (s a₁) ∙ ap p' (α a₁)

    σ-pres : 𝓤 ⊔ 𝓥 ̇
    σ-pres = (a₁ : A₁) → ap f₁ (σ a₁) ≡ aux-γ a₁ ∙ σ' (f₁ a₁)

    aux-δ : f₂ ∘ s ∘ p ∼ s' ∘ p' ∘ f₂
    aux-δ a₂ = α (p a₂) ∙ ap s' (β a₂)

    ρ-pres : 𝓤 ⊔ 𝓥 ̇
    ρ-pres = (a₂ : A₂) → ap f₂ (ρ a₂) ≡ aux-δ a₂ ∙ ρ' (f₂ a₂)

    aux-ε-γ₁ : f₂ ∘ s ∘ p ∘ s ∼ s' ∘ p' ∘ s' ∘ f₁
    aux-ε-γ₁ a₁ = α (p (s a₁)) ∙ ap s' (aux-γ a₁)

    aux-ε-δ₁ : f₂ ∘ s ∘ p ∘ s ∼ s' ∘ p' ∘ s' ∘ f₁
    aux-ε-δ₁ a₁ = aux-δ (s a₁) ∙ ap s' (ap p' (α a₁))

    aux-ε-γ₁-is-aux-ε-δ₁ : aux-ε-γ₁ ∼ aux-ε-δ₁
    aux-ε-γ₁-is-aux-ε-δ₁ a₁ = (refl (α (p (s a₁))) ✦ ap-∙ s' _ _) ∙ ∙-assoc _ _ _

    module _ (γ : σ-pres) (δ : ρ-pres) where

      aux-ε-γ₂ : (a₁ : A₁) → ap f₂ (ap s (σ a₁)) ∙ α a₁ ≡ aux-ε-γ₁ a₁ ∙ ap s' (σ' (f₁ a₁))
      aux-ε-γ₂ a₁ = (ap-∘ s f₂ (σ a₁) ✦ refl (α a₁)) ∙ hnat α (σ a₁) ⁻¹ ∙ (refl (α (p (s a₁))) ✦ (ap-∘ f₁ s' (σ a₁) ⁻¹ ∙ ap (ap s') (γ a₁) ∙ ap-∙ s' _ _)) ∙ ∙-assoc _ _ _

      aux-ε-δ₂ : (a₁ : A₁) → ap f₂ (ρ (s a₁)) ∙ α a₁ ≡ aux-ε-δ₁ a₁ ∙ ρ' (s' (f₁ a₁))
      aux-ε-δ₂ a₁ = (δ (s a₁) ✦ ap-id (α a₁) ⁻¹) ∙ ∙-assoc _ _ _ ⁻¹ ∙ (refl (aux-δ (s a₁)) ✦ (hnat ρ' (α a₁) ∙ (ap-∘ p' s' (α a₁) ⁻¹ ✦ refl (ρ' (s' (f₁ a₁)))))) ∙ ∙-assoc _ _ _

      τ-pres : 𝓤 ⊔ 𝓥 ̇
      τ-pres = (a₁ : A₁) → (ap (ap f₂) (τ a₁) ✦ refl (α a₁)) ∙ aux-ε-δ₂ a₁ ≡ aux-ε-γ₂ a₁ ∙ (aux-ε-γ₁-is-aux-ε-δ₁ a₁ ✦ τ' (f₁ a₁))

  ishae-pres : (α : s-pres) → 𝓤 ⊔ 𝓥 ̇
  ishae-pres α = Σ β ꞉ p-pres , Σ γ ꞉ σ-pres α β , Σ δ ꞉ ρ-pres α β , τ-pres α β γ δ

  hae-pres : 𝓤 ⊔ 𝓥 ̇
  hae-pres = Σ α ꞉ s-pres , ishae-pres α


-- IV. Equivalence Preservation is Function Preservation

module EqvPres-is-FunPres where

  abstract

    module _ (A : 𝓤 ̇) (B : 𝓥 ̇) (f : A → B) where

      open Preservation-of-Equivalences A A (≃-refl A) B B (≃-refl B) f f 

      ishae-pres-is-Contr' : isContr (ishae-pres (hrefl _))
      ishae-pres-is-Contr' = ≃-preserves-Contr (≃-sym (Σ-assoc _ _ _ ● Σ-over-Contr-base-is-fib _ _ Contrβγ)) Contrδε where

        Contrβγ : isContr (Σ β ꞉ p-pres , σ-pres (hrefl _) β)
        Contrβγ = ≃-preserves-Contr
          (split , (dep-Σ-UMP A (λ a → f a ≡ f a) λ a βa → refl (f a) ≡ (βa ∙ refl (f a)) ∙ refl (f a)))
          (Π-preserves-Contr _ (λ a → ≃-preserves-Contr (Σ-preserves-family-≃ (λ βa → post-∙-≃ (refl (f a)) (ru βa ∙ ru _))) (free-right-endpt-is-Contr _ _)))  

        Contrδε : isContr (Σ δ ꞉ ρ-pres (hrefl _) (hrefl _) , τ-pres (hrefl _) (hrefl _) (hrefl _) δ)
        Contrδε = ≃-preserves-Contr
          (split , (dep-Σ-UMP A (λ a → refl (f a) ≡ refl _ ∙ refl _ ∙ refl _) λ a δa → refl _ ∙ (refl _ ∙ δa ∙ refl _ ∙ refl _ ∙ refl _ ∙ refl _ ∙ refl _) ≡ refl (refl (f a))))
          (Π-preserves-Contr _ (λ a → ≃-preserves-Contr (Σ-preserves-family-≃ (λ δa → pre-∙-≃ (refl (refl (f a))) (lu _ ⁻¹ ∙ ru _ ⁻¹ ∙ ru _ ⁻¹ ∙ ru _ ⁻¹ ∙ ru _ ⁻¹ ∙ ru _ ⁻¹ ∙ lu δa ⁻¹))) (free-left-endpt-is-Contr _ _)))

    open Preservation-of-Equivalences

    ishae-pres-is-Contr : (A₁ A₂ : 𝓤 ̇) (e : A₁ ≃ A₂) (B₁ B₂ : 𝓥 ̇) (e' : B₁ ≃ B₂) (f₁ : A₁ → B₁) (f₂ : A₂ → B₂) (α : f₂ ∘ pr₁ e ∼ pr₁ e' ∘ f₁) → isContr (ishae-pres A₁  A₂ e B₁ B₂ e' f₁ f₂ α)
    ishae-pres-is-Contr {𝓤} {𝓥} = 𝕁-≃ (λ A₁ A₂ e → (B₁ B₂ : 𝓥 ̇) (e' : B₁ ≃ B₂) (f₁ : A₁ → B₁) (f₂ : A₂ → B₂) (α : f₂ ∘ pr₁ e ∼ pr₁ e' ∘ f₁) → isContr (ishae-pres A₁ A₂ e B₁ B₂ e' f₁ f₂ α)) λ A →
      𝕁-≃ (λ B₁ B₂ e' → (f₁ : A → B₁) (f₂ : A → B₂) (α : f₂ ∘ id ∼ pr₁ e' ∘ f₁) → isContr (ishae-pres A A (≃-refl A) B₁ B₂ e' f₁ f₂ α)) λ B f₁ f₂ →
        𝕁-∼ (λ f₂ f₁ α → isContr (ishae-pres A A (≃-refl A) B B (≃-refl B) f₁ f₂ α)) (λ f → ishae-pres-is-Contr' A B f) f₂ f₁

  hae-pres-≃-fun-pres : (A₁ A₂ : 𝓤 ̇) (e : A₁ ≃ A₂) (B₁ B₂ : 𝓥 ̇) (e' : B₁ ≃ B₂) (f₁ : A₁ → B₁) (f₂ : A₂ → B₂) → hae-pres A₁ A₂ e B₁ B₂ e' f₁ f₂ ≃ (f₂ ∘ pr₁ e ∼ pr₁ e' ∘ f₁)
  hae-pres-≃-fun-pres A₁ A₂ e B₁ B₂ e' f₁ f₂ = Σ-of-Contr-family-is-base _ _ (ishae-pres-is-Contr A₁ A₂ e B₁ B₂ e' f₁ f₂)

  fun-to-hae : (A₁ A₂ : 𝓤 ̇) (e : A₁ ≃ A₂) (B₁ B₂ : 𝓥 ̇) (e' : B₁ ≃ B₂) (f₁ : A₁ → B₁) (f₂ : A₂ → B₂) → (f₂ ∘ pr₁ e ∼ pr₁ e' ∘ f₁) → hae-pres A₁ A₂ e B₁ B₂ e' f₁ f₂
  fun-to-hae A₁ A₂ e B₁ B₂ e' f₁ f₂ = inv (hae-pres-≃-fun-pres A₁ A₂ e B₁ B₂ e' f₁ f₂)

open EqvPres-is-FunPres public
open Preservation-of-Equivalences hiding (s ; p ; σ ; ρ ; τ) public

-- V. Fibered Algebras and their Sections

module Fibered-Algebras where

  -- Map of total spaces induced by base function and function over.

  total↓ : {A : 𝓤 ̇} {B : 𝓥 ̇} {P : A → 𝓦 ̇} (Q : B → 𝓣 ̇) (f : A → B) → ((a : A) → P a → Q (f a)) → Σ P → Σ Q
  total↓ Q f g (a , u) = f a , g a u

  {- Note: the following definition of FibAlg is unconventional but convenient for the derivation of inductivity from initiality. In practice, a more direct definition will be used, such as

[Import stuff from ℤ-Algebras]

Ultimately, however, any representation which is to be justified by the argument below should map into our definition of FibAlg. More precisely, it should induce an algebra structure on the total space of the type family and a morphism structure on the projection. The reason why we can use the more abstract definition is that the notion of algebra section is independent of these details, to a certain extent (the propositional computation rules for higher constructors aren't).  -}

  -- Fibered Algebras

  FibAlgStr : (A : Alg 𝓤) → (pr₁ A → 𝓥 ̇) → 𝓤 ⊔ 𝓥 ̇
  FibAlgStr (A , a₀ , s , i) E = E a₀ × (Σ s' ꞉ ((a : A) → E a → E (s a)) , isequiv (total↓ E s s'))

  FibAlg : (𝓥 : Universe) → Alg 𝓤 → 𝓤 ⊔ 𝓥 ⁺ ̇
  FibAlg 𝓥 A = Σ E ꞉ (pr₁ A → 𝓥 ̇) , FibAlgStr A E

  -- Associated algebra on total space

  TotAlg : (A : Alg 𝓤) → FibAlg 𝓥 A → Alg (𝓤 ⊔ 𝓥)
  TotAlg (A , a₀ , s , i) (E , e₀ , s' , j) = (Σ E) , (a₀ , e₀) , (total↓ E s s' , j)

  -- Projection of associated algebra is a morphism

  π₁ : (A : Alg 𝓤) (E : FibAlg 𝓥 A) → Hom (TotAlg A E) A
  π₁ (A , a₀ , s , i) (E , e₀ , s' , j) = pr₁ , refl a₀ , hrefl (s ∘ pr₁)

  -- Fibered algebra sections

  AlgSecStr : (A : Alg 𝓤) (E : FibAlg 𝓥 A) → ((a : pr₁ A) → (pr₁ E) a) → 𝓤 ⊔ 𝓥 ̇
  AlgSecStr (A , a₀ , s , i) (E , e₀ , s' , j) f = (f a₀ ≡ e₀) × ((a : A) → f (s a) ≡ s' a (f a))

  AlgSec : (A : Alg 𝓤) → FibAlg 𝓥 A → 𝓤 ⊔ 𝓥 ̇
  AlgSec A E = Σ f ꞉ Π (pr₁ E) , AlgSecStr A E f 

  -- Section induces morphism into associated algebra

  sec-to-hom : (A : Alg 𝓤) (E : FibAlg 𝓥 A) → AlgSec A E → Hom A (TotAlg A E)
  sec-to-hom (A , a₀ , s , i) (E , e₀ , s' , j) (f , f₀ , f-s) = (λ a → a , f a) , dpair-≡ (refl a₀ , f₀) , λ a → dpair-≡ (refl (s a) , f-s a)

  -- Sections are sections

  sec-to-hom-gives-section : (A : Alg 𝓤) (E : FibAlg 𝓥 A) (f : AlgSec A E) → comp A (TotAlg A E) A (π₁ A E) (sec-to-hom A E f) ≡ algid A
  sec-to-hom-gives-section (A , a₀ , s , i) (E , e₀ , s' , j) (f , f₀ , f-s) =
    Hom-≡-intro (A , a₀ , s , i) (A , a₀ , s , i) _ _ (
      hrefl _ ,
      (lu _ ⁻¹ ∙ (ru _ ⁻¹ ∙ dpr₁-≡-β (refl a₀) f₀)) ,
      λ a → ru _ ⁻¹ ∙ ru _ ⁻¹ ∙ dpr₁-≡-β (refl (s a)) (f-s a)
      )

  -- Fibered algebra induced by a constant algebra

  Alg-to-FibAlg : (A : Alg 𝓤) (B : Alg 𝓥) → FibAlg 𝓥 A
  Alg-to-FibAlg {𝓤} {𝓥} (A , a₀ , s , p , σ , ρ , τ) (B , b₀ , s' , p' , σ' , ρ' , τ') = E , b₀ , (λ a → s') , qinv-to-isequiv (g , α , β) where
    E : A → 𝓥 ̇
    E a = B
    f : Σ E → Σ E
    f (a , b) = s a , s' b 
    g : Σ E → Σ E
    g (a , b) = (p a) , (p' b)
    α : f ∘ g ∼ id
    α (a , b) = dpair-≡ (ρ a , (transportconst B (ρ a) (s' (p' b)) ∙ ρ' b))
    β : g ∘ f ∼ id
    β (a , b) = dpair-≡ (σ a , (transportconst B (σ a) (p' (s' b)) ∙ σ' b))
    
open Fibered-Algebras public


-- VI. Inductive Algebras

module Inductive-Algebras where

  isind : (𝓥 : Universe) → Alg 𝓤 → 𝓤 ⊔ 𝓥 ⁺ ̇
  isind 𝓥 A = (E : FibAlg 𝓥 A) → AlgSec A E

open Inductive-Algebras public


-- VII. Initial Algebras

module Homotopy-Initial-Algebras where

  isinit : (𝓥 : Universe) → Alg 𝓤 → 𝓤 ⊔ 𝓥 ⁺ ̇
  isinit 𝓥 A = (B : Alg 𝓥) → isContr (Hom A B)

  isinit-is-Prop : (𝓥 : Universe) (A : Alg 𝓤) → isProp (isinit 𝓥 A)
  isinit-is-Prop 𝓥 A = Π-preserves-Props _ (λ B → isContr-is-Prop _)

  hasrec : (𝓥 : Universe) → Alg 𝓤 → 𝓤 ⊔ 𝓥 ⁺ ̇
  hasrec 𝓥 A = (B : Alg 𝓥) → Hom A B

  hasrecunique : (𝓥 : Universe) (A : Alg 𝓤) → 𝓤 ⊔ 𝓥 ⁺ ̇
  hasrecunique 𝓥 A = (B : Alg 𝓥) → isProp (Hom A B)

open Homotopy-Initial-Algebras public


-- VIII. The Integers as Signed Natural Numbers

module Integers-as-Signed-Nats where

  data ℤω : 𝓤₀ ̇ where
    0ω : ℤω
    strpos : ℕ → ℤω
    strneg : ℕ → ℤω

  -- ℤω is a ℤ-algebra

  succω : ℤω → ℤω
  succω 0ω = strpos 0
  succω (strpos n) = strpos (succ n)
  succω (strneg 0) = 0ω
  succω (strneg (succ n)) = strneg n

  predω : ℤω → ℤω
  predω 0ω = strneg 0
  predω (strpos 0) = 0ω
  predω (strpos (succ n)) = strpos n
  predω (strneg n) = strneg (succ n)

  secω : (z : ℤω) → predω (succω z) ≡ z
  secω 0ω = refl _
  secω (strpos n) = refl _
  secω (strneg 0) = refl _
  secω (strneg (succ n)) = refl _

  retω : (z : ℤω) → succω (predω z) ≡ z
  retω 0ω = refl _
  retω (strpos 0) = refl _
  retω (strpos (succ n)) = refl _
  retω (strneg n) = refl _

  cohω : (z : ℤω) → ap succω (secω z) ≡ retω (succω z)
  cohω 0ω = refl _
  cohω (strpos n) = refl _
  cohω (strneg 0) = refl _
  cohω (strneg (succ n)) = refl _

  ℤω-≃ : ℤω ≃ ℤω
  ℤω-≃ = (succω , predω , secω , retω , cohω)
  
  ℤω-alg : Alg 𝓤₀
  ℤω-alg = ℤω , 0ω , ℤω-≃

open Integers-as-Signed-Nats public


-- VIII. ℤω is initial

module ℤω-is-initial where

  ℤω-has-rec : hasrec 𝓤 ℤω-alg
  ℤω-has-rec (A , a₀ , s , p , σ , ρ , τ) = f , refl _ , f-s where
    f : ℤω → A
    f 0ω = a₀
    f (strpos zero) = s a₀
    f (strpos (succ n)) = s (f (strpos n))
    f (strneg zero) = p a₀
    f (strneg (succ n)) = p (f (strneg n))
    f-s : f ∘ succω ∼ s ∘ f
    f-s 0ω = refl _
    f-s (strpos n) = refl _
    f-s (strneg zero) = ρ _ ⁻¹
    f-s (strneg (succ n)) = ρ _ ⁻¹

  ℤω-has-rec-unique : hasrecunique 𝓤 ℤω-alg
  ℤω-has-rec-unique {𝓤} (A , a₀ , s , p , σ , ρ , τ) (f , f₀ , f-s) (g , g₀ , g-s) = Hom-≡-intro ℤω-alg A' _ _ (H , H₀ , H-s) where
    A' : Alg 𝓤
    A' = (A , a₀ , s , p , σ , ρ , τ)
    e : A ≃ A
    e = (s , p , σ , ρ , τ)
    f-i : ishae-pres ℤω ℤω ℤω-≃ A A e f f f-s
    f-i = pr₁ (ishae-pres-is-Contr ℤω ℤω ℤω-≃ A A e f f f-s)
    f-p : f ∘ predω ∼ p ∘ f
    f-p = pr₁ f-i
    f-σ : (z : ℤω) → ap f (secω z) ≡ f-p (succω z) ∙ ap p (f-s z) ∙ σ (f z)
    f-σ = pr₁ (pr₂ f-i)
    f-ρ : (z : ℤω) → ap f (retω z) ≡ f-s (predω z) ∙ ap s (f-p z) ∙ ρ (f z)
    f-ρ = pr₁ (pr₂ (pr₂ f-i))
    g-i : ishae-pres ℤω ℤω ℤω-≃ A A e g g g-s
    g-i = pr₁ (ishae-pres-is-Contr ℤω ℤω ℤω-≃ A A e g g g-s)
    g-p : g ∘ predω ∼ p ∘ g
    g-p = pr₁ g-i
    g-σ : (z : ℤω) → ap g (secω z) ≡ g-p (succω z) ∙ ap p (g-s z) ∙ σ (g z)
    g-σ = pr₁ (pr₂ g-i)
    g-ρ : (z : ℤω) → ap g (retω z) ≡ g-s (predω z) ∙ ap s (g-p z) ∙ ρ (g z)
    g-ρ = pr₁ (pr₂ (pr₂ g-i))
    H : f ∼ g
    H 0ω = f₀ ∙ g₀ ⁻¹
    H (strpos zero) = f-s 0ω ∙ ap s (H 0ω) ∙ g-s 0ω ⁻¹
    H (strpos (succ n)) = f-s (strpos n) ∙ ap s (H (strpos n)) ∙ g-s (strpos n) ⁻¹
    H (strneg zero) = f-p 0ω ∙ ap p (H 0ω) ∙ g-p 0ω ⁻¹
    H (strneg (succ n)) = f-p (strneg n) ∙ ap p (H (strneg n)) ∙ g-p (strneg n) ⁻¹
    H₀ :  (f₀ ∙ g₀ ⁻¹) ⁻¹ ∙ f₀ ≡ g₀
    H₀ = (distr _ _ ∙ᵣ f₀) ∙ ∙-assoc _ _ _ ⁻¹ ∙ (g₀ ⁻¹ ⁻¹ ∙ₗ linv _) ∙ ru _ ⁻¹ ∙ ⁻¹-invol _
    H-s :  (z : ℤω) → f-s z ∙ ap s (H z) ≡  H (succω z) ∙ g-s z
    H-s 0ω = ru _ ∙ ((f-s 0ω ∙ ap s (H 0ω)) ∙ₗ linv _ ⁻¹) ∙ ∙-assoc _ _ _
    H-s (strpos zero) = ru _ ∙ ((f-s (strpos zero) ∙ ap s (f-s 0ω ∙ ap s (f₀ ∙ g₀ ⁻¹) ∙ g-s 0ω ⁻¹)) ∙ₗ linv _ ⁻¹) ∙ ∙-assoc _ _ _ 
    H-s (strpos (succ n)) = ru _ ∙ ((f-s (strpos (succ n)) ∙ ap s (f-s (strpos n) ∙ ap s (H (strpos n)) ∙ g-s (strpos n) ⁻¹)) ∙ₗ linv _ ⁻¹) ∙ ∙-assoc _ _ _ 
    H-s (strneg zero) =
      f-s (strneg zero) ∙ ap s (f-p 0ω ∙ ap p (H 0ω) ∙ g-p 0ω ⁻¹)
        ≡⟨ f-s (strneg zero) ∙ₗ ap-∙ s _ _ ⟩
      f-s (strneg zero) ∙ (ap s (f-p 0ω ∙ ap p (H 0ω)) ∙ ap s (g-p 0ω ⁻¹))
        ≡⟨ ap (λ - → f-s (strneg zero) ∙ (- ∙ ap s (g-p 0ω ⁻¹))) (ap-∙ s _ _) ⟩
      f-s (strneg zero) ∙ (ap s (f-p 0ω) ∙ ap s (ap p (H 0ω)) ∙ ap s (g-p 0ω ⁻¹))
        ≡⟨ ∙-assoc _ _ _ ∙ (∙-assoc _ _ _ ∙ᵣ ap s (g-p 0ω ⁻¹)) ⟩
      f-s (strneg zero) ∙ ap s (f-p 0ω) ∙ ap s (ap p (H 0ω)) ∙ ap s (g-p 0ω ⁻¹)
        ≡⟨ ap (λ - → - ∙ ap s (ap p (H 0ω)) ∙ ap s (g-p 0ω ⁻¹)) ((lu _ ∙ (f-ρ 0ω ∙ᵣ ρ (f 0ω) ⁻¹) ∙ ∙-assoc _ _ _ ⁻¹ ∙ ((f-s (strneg zero) ∙ ap s (f-p 0ω)) ∙ₗ rinv _) ∙ ru _ ⁻¹) ⁻¹ ) ⟩
      ρ (f 0ω) ⁻¹ ∙ ap s (ap p (H 0ω)) ∙ ap s (g-p 0ω ⁻¹)
        ≡⟨ ap (λ - → ρ (f 0ω) ⁻¹ ∙ - ∙ ap s (g-p 0ω ⁻¹)) (ap-∘ p s (H 0ω))  ⟩
      ρ (f 0ω) ⁻¹ ∙ ap (s ∘ p) (H 0ω) ∙ ap s (g-p 0ω ⁻¹)
        ≡⟨ hnat (hsym ρ) (H 0ω) ∙ᵣ ap s (g-p 0ω ⁻¹) ⟩
      ap id (H 0ω) ∙ ρ (g 0ω) ⁻¹ ∙ ap s (g-p 0ω ⁻¹)
        ≡⟨ ∙-assoc _ _ _ ⁻¹ ∙ (ap-id _ ✦ ((ρ (g 0ω) ⁻¹ ∙ₗ ap-⁻¹  s _) ∙ distr _ _ ⁻¹ ∙ lu _ ∙ ((g-ρ 0ω ∙ ∙-assoc _ _ _ ⁻¹) ∙ᵣ ((ap s (g-p 0ω) ∙ ρ (g 0ω)) ⁻¹)) ∙ ∙-assoc _ _ _ ⁻¹ ∙ (g-s (strneg zero) ∙ₗ rinv _) ∙ ru _ ⁻¹)) ⟩
      H 0ω ∙ g-s (strneg zero) ∎ 
    H-s (strneg (succ n)) =
      f-s (strneg (succ n)) ∙ ap s (f-p (strneg n) ∙ ap p (H (strneg n)) ∙ g-p (strneg n) ⁻¹)
        ≡⟨ f-s (strneg (succ n)) ∙ₗ ap-∙ s _ _ ⟩
      f-s (strneg (succ n)) ∙ (ap s (f-p (strneg n) ∙ ap p (H (strneg n))) ∙ ap s (g-p (strneg n) ⁻¹))
        ≡⟨ ap (λ - → f-s (strneg (succ n)) ∙ (- ∙ ap s (g-p (strneg n) ⁻¹))) (ap-∙ s _ _) ⟩
      f-s (strneg (succ n)) ∙ (ap s (f-p (strneg n)) ∙ ap s (ap p (H (strneg n))) ∙ ap s (g-p (strneg n) ⁻¹))
        ≡⟨ ∙-assoc _ _ _ ∙ (∙-assoc _ _ _ ∙ᵣ ap s (g-p (strneg n) ⁻¹)) ⟩
      f-s (strneg (succ n)) ∙ ap s (f-p (strneg n)) ∙ ap s (ap p (H (strneg n))) ∙ ap s (g-p (strneg n) ⁻¹)
        ≡⟨ ap (λ - → - ∙ ap s (ap p (H (strneg n))) ∙ ap s (g-p (strneg n) ⁻¹)) ((lu _ ∙ (f-ρ (strneg n) ∙ᵣ ρ (f (strneg n)) ⁻¹) ∙ ∙-assoc _ _ _ ⁻¹ ∙ ((f-s (strneg (succ n)) ∙ ap s (f-p (strneg n))) ∙ₗ rinv _) ∙ ru _ ⁻¹) ⁻¹ ) ⟩
      ρ (f (strneg n)) ⁻¹ ∙ ap s (ap p (H (strneg n))) ∙ ap s (g-p (strneg n) ⁻¹)
        ≡⟨ ap (λ - → ρ (f (strneg n)) ⁻¹ ∙ - ∙ ap s (g-p (strneg n) ⁻¹)) (ap-∘ p s (H (strneg n)))  ⟩
      ρ (f (strneg n)) ⁻¹ ∙ ap (s ∘ p) (H (strneg n)) ∙ ap s (g-p (strneg n) ⁻¹)
        ≡⟨ hnat (hsym ρ) (H (strneg n)) ∙ᵣ ap s (g-p (strneg n) ⁻¹) ⟩
      ap id (H (strneg n)) ∙ ρ (g (strneg n)) ⁻¹ ∙ ap s (g-p (strneg n) ⁻¹)
        ≡⟨ ∙-assoc _ _ _ ⁻¹ ∙ (ap-id _ ✦ ((ρ (g (strneg n)) ⁻¹ ∙ₗ ap-⁻¹  s _) ∙ distr _ _ ⁻¹ ∙ lu _ ∙ ((g-ρ (strneg n) ∙ ∙-assoc _ _ _ ⁻¹) ∙ᵣ ((ap s (g-p (strneg n)) ∙ ρ (g (strneg n))) ⁻¹)) ∙ ∙-assoc _ _ _ ⁻¹ ∙ (g-s (strneg (succ n)) ∙ₗ rinv _) ∙ ru _ ⁻¹)) ⟩
      H (strneg n) ∙ g-s (strneg (succ n)) ∎

  ℤω-is-init : isinit 𝓤 ℤω-alg
  ℤω-is-init A = pr₂ isContr-iff-is-inhabited-Prop (ℤω-has-rec A , ℤω-has-rec-unique A)


-- IX. Initial algebras are inductive

module Initial-to-Inductive where

  isinit-to-isind : (A : Alg 𝓤) → isinit 𝓤 A → isind 𝓤 A
  isinit-to-isind {𝓤} (A , a₀ , s , i) init (E , e₀ , s' , j) = g , g₀ , g-s
 
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

    -- 3. Description of composite morphism π₁∘f

    π₁∘f : Hom A' A'
    π₁∘f = comp A' T A' (π₁ A' E') A-rec

    _ : pr₁ (π₁∘f) ≡ f₁
    _ = refl _

    f₁₀ : f₁ a₀ ≡ a₀
    f₁₀ = ap pr₁ f₀ ∙ refl a₀
    
    _ : f₁₀ ≡ pr₁ (pr₂ π₁∘f)
    _ = refl _

    f₁-β : f₁ ∘ s ∼ s ∘ f₁
    f₁-β a = ap pr₁ (f-s a) ∙ refl _
    _ : f₁-β ≡ pr₂ (pr₂ π₁∘f)
    _ = refl _

    -- 3.1 First components of f agree with composite π₁∘f

    path-agreement : f₀₁ ≡ f₁₀
    path-agreement = ap pr₁ (dpr-≡-agreement f₀) ∙ ru _

    htpy-agreement : f-s₁ ∼ f₁-β
    htpy-agreement a = ap pr₁ (dpr-≡-agreement (f-s a)) ∙ ru _

    -- 4. Initiality gives path from π₁∘f to algid A'

    A-uniqueness : isProp (Hom A' A')
    A-uniqueness = pr₂ (pr₁ isContr-iff-is-inhabited-Prop (init A'))    
    
    path : (comp A' T A' (π₁ A' E') A-rec) ≡ algid A'
    path = A-uniqueness _ _

    -- 4.1 Extension of path

    pathext : HomId A' A' (comp A' T A' (π₁ A' E') A-rec) (algid A')
    pathext = Hom-≡-elim A' A' _ _ path

    H : f₁ ∼ id
    H = pr₁ pathext

    H₀ : H a₀ ⁻¹ ∙ f₁₀ ≡ refl a₀
    H₀ = pr₁ (pr₂ pathext)

    H-β : (a : A) → f₁-β a ∙ ap s (H a) ≡ H (s a) ∙ refl (s a) 
    H-β = pr₂ (pr₂ pathext)

    -- 4.2 Rearranging

    H₀' : H a₀ ≡ f₁₀
    H₀' = ru _ ∙ (H a₀ ∙ₗ H₀ ⁻¹) ∙ ∙-assoc _ _ _ ∙ (rinv _ ∙ᵣ f₁₀) ∙ lu _ ⁻¹

    H-β' : (a : A) → H (s a) ≡ f₁-β a ∙ ap s (H a)
    H-β' a = ru _ ∙ H-β a ⁻¹

    -- 5. Construction of section

    g : (a : A) → E a
    g a = transport E (H a) (f₂ a)

    g₀ : g a₀ ≡ e₀
    g₀ = transport E (H a₀) (f₂ a₀)
             ≡⟨ ap (λ - → transport E - (f₂ a₀)) H₀' ⟩
           transport E f₁₀ (f₂ a₀)
             ≡⟨ ap (λ - → transport E - (f₂ a₀)) (path-agreement ⁻¹) ⟩
           transport E f₀₁ (f₂ a₀)
             ≡⟨ f₀₂ ⟩
           e₀ ∎
           
    g-s : (a : A) → g (s a) ≡ s' a (g a)
    g-s a = transport E (H (s a)) (f₂ (s a))
              ≡⟨ ap (λ - → transport E - (f₂ (s a))) (H-β' a) ⟩
            transport E (f₁-β a ∙ ap s (H a)) (f₂ (s a))
              ≡⟨ transport-∙ E (f₁-β a) (ap s (H a)) (f₂ (s a)) ⁻¹ ⟩
            transport E (ap s (H a)) (transport E (f₁-β a) (f₂ (s a)))
              ≡⟨ ap (λ - → transport E (ap s (H a)) (transport E - (f₂ (s a)))) (htpy-agreement a ⁻¹)  ⟩
            transport E (ap s (H a)) (transport E (f-s₁ a) (f₂ (s a)))
              ≡⟨ ap (transport E (ap s (H a))) (f-s₂ a) ⟩
            transport E (ap s (H a)) (s' (f₁ a) (f₂ a))
              ≡⟨ ℍ (f₁ a) (λ b p → transport E (ap s p) (s' (f₁ a) (f₂ a)) ≡ s' b (transport E p (f₂ a))) (refl _) a (H a) ⟩
            s' a (transport E (H a) (f₂ a)) ∎


-- X. Inductive algebras are initial 

module Inductive-to-Initial where

  isind-to-hasrec : (A : Alg 𝓤) → isind 𝓤 A → hasrec 𝓤 A
  isind-to-hasrec A A-ind B = A-ind (Alg-to-FibAlg A B)

  isind-to-hasrecunique : (A : Alg 𝓤) → isind 𝓤 A → hasrecunique 𝓤 A
  isind-to-hasrecunique {𝓤} (A , a₀ , s , p , σ , ρ , τ)  A-ind (B , b₀ , s' , p' , σ' , ρ' , τ') (f , f₀ , f-s) (g , g₀ , g-s) = Hom-≡-intro A' B' _ _ (H , H₀' , H-s') where
    A' : Alg 𝓤
    A' = (A , a₀ , s , p , σ , ρ , τ)
    B' : Alg 𝓤
    B' = (B , b₀ , s' , p' , σ' , ρ' , τ')
    f-i : ishae-pres A A (s , p , σ , ρ , τ) B B (s' , p' , σ' , ρ' , τ') f f f-s
    f-i = pr₁ (ishae-pres-is-Contr A A (s , p , σ , ρ , τ) B B (s' , p' , σ' , ρ' , τ') f f f-s)
    f-p : f ∘ p ∼ p' ∘ f
    f-p = pr₁ f-i
    f-σ : (a : A) → ap f (σ a) ≡ f-p (s a) ∙ ap p' (f-s a) ∙ σ' (f a)
    f-σ = pr₁ (pr₂ f-i)
    f-ρ : (a : A) → ap f (ρ a) ≡ f-s (p a) ∙ ap s' (f-p a) ∙ ρ' (f a)
    f-ρ = pr₁ (pr₂ (pr₂ f-i))
    g-i : ishae-pres A A (s , p , σ , ρ , τ) B B (s' , p' , σ' , ρ' , τ') g g g-s
    g-i = pr₁ (ishae-pres-is-Contr A A (s , p , σ , ρ , τ) B B (s' , p' , σ' , ρ' , τ') g g g-s)
    g-p : g ∘ p ∼ p' ∘ g
    g-p = pr₁ g-i
    g-σ : (a : A) → ap g (σ a) ≡ g-p (s a) ∙ ap p' (g-s a) ∙ σ' (g a)
    g-σ = pr₁ (pr₂ g-i)
    g-ρ : (a : A) → ap g (ρ a) ≡ g-s (p a) ∙ ap s' (g-p a) ∙ ρ' (g a)
    g-ρ = pr₁ (pr₂ (pr₂ g-i))
    ϕ : (Σ a ꞉ A , f a ≡ g a) → (Σ a ꞉ A , f a ≡ g a)
    ϕ (a , ih) = (s a) , (f-s a ∙ ap s' ih ∙ g-s a ⁻¹)
    ψ : (Σ a ꞉ A , f a ≡ g a) → (Σ a ꞉ A , f a ≡ g a)
    ψ (a , ih) = p a , (f-p a ∙ ap p' ih ∙ g-p a ⁻¹) 
    α : ϕ ∘ ψ ∼ id
    α (a , ih) = dpair-≡ (ρ a , (transport-funval-≡ f g (ρ a) (f-s (p a) ∙ ap s' (f-p a ∙ ap p' ih ∙ g-p a ⁻¹) ∙ g-s (p a) ⁻¹) ∙ ((ap _⁻¹ (f-ρ a)  ✦ refl _ ✦ g-ρ a) ∙ aux-path (f-s (p a)) (g-s (p a)) (f-p a) (g-p a) ih))) where
      aux-path : {b₁ b₂ b₃ b₄ x y : B} (p₁ : b₁ ≡ _) (p₂ : b₂ ≡ _) (p₃ : b₃ ≡ _) (p₄ : b₄ ≡ _) (ih : x ≡ y) → (p₁ ∙ ap s' p₃ ∙ ρ' x) ⁻¹ ∙ (p₁ ∙ ap s' (p₃ ∙ ap p' ih ∙ p₄ ⁻¹) ∙ p₂ ⁻¹) ∙ (p₂ ∙ ap s' p₄ ∙ ρ' y) ≡ ih
      aux-path (refl _) (refl _) (refl _) (refl _) (refl _) = (ru _ ⁻¹ ∙ᵣ (refl _ ∙ ρ' _)) ∙ linv _ 
    β : ψ ∘ ϕ ∼ id
    β (a , ih) = dpair-≡ (σ a , (transport-funval-≡ f g (σ a) (f-p (s a) ∙ ap p' (f-s a ∙ ap s' ih ∙ g-s a ⁻¹) ∙ g-p (s a) ⁻¹) ∙ ((ap _⁻¹ (f-σ a) ✦ refl _ ✦ g-σ a) ∙ aux-path (f-p (s a)) (g-p (s a)) (f-s a) (g-s a) ih))) where
      aux-path : {b₁ b₂ b₃ b₄ x y : B} (p₁ : b₁ ≡ _) (p₂ : b₂ ≡ _) (p₃ : b₃ ≡ _) (p₄ : b₄ ≡ _) (ih : x ≡ y) → (p₁ ∙ ap p' p₃ ∙ σ' x) ⁻¹ ∙ (p₁ ∙ ap p' (p₃ ∙ ap s' ih ∙ p₄ ⁻¹) ∙ p₂ ⁻¹) ∙ (p₂ ∙ ap p' p₄ ∙ σ' y) ≡ ih
      aux-path (refl _) (refl _) (refl _) (refl _) (refl _) = (ru _ ⁻¹ ∙ᵣ (refl _ ∙ σ' _)) ∙ linv _
    E : FibAlg 𝓤 A'
    E = (λ a → f a ≡ g a) , (f₀ ∙ g₀ ⁻¹) , (λ a ih → f-s a ∙ ap s' ih ∙ g-s a ⁻¹) , qinv-to-isequiv (ψ , α , β)
    H : f ∼ g
    H = pr₁ (A-ind E)
    H₀ : H a₀ ≡ f₀ ∙ g₀ ⁻¹
    H₀ = pr₁ (pr₂ (A-ind E))
    H-s : (a : A) → H (s a) ≡ f-s a ∙ ap s' (H a) ∙ g-s a ⁻¹
    H-s = pr₂ (pr₂ (A-ind E))
    H₀' : H a₀ ⁻¹ ∙ f₀ ≡ g₀
    H₀' = ((ap _⁻¹ H₀ ∙ distr _ _) ∙ᵣ f₀) ∙ ∙-assoc _ _ _ ⁻¹ ∙ (g₀ ⁻¹ ⁻¹ ∙ₗ linv _) ∙ ru _ ⁻¹ ∙ ⁻¹-invol _
    H-s' : (a : A) → f-s a ∙ ap s' (H a) ≡ H (s a) ∙ g-s a
    H-s' a = ((H-s a ∙ᵣ g-s a) ∙ ∙-assoc _ _ _ ⁻¹ ∙ ((f-s a ∙ ap s' (H a)) ∙ₗ linv _) ∙ ru _ ⁻¹) ⁻¹

  isind-to-isinit : (A : Alg 𝓤) → isind 𝓤 A → isinit 𝓤 A
  isind-to-isinit A A-ind B = pr₂ isContr-iff-is-inhabited-Prop (isind-to-hasrec A A-ind B , isind-to-hasrecunique A A-ind B)

open Inductive-to-Initial public


--------------------------------------------------------------------------------

-- Fibered Algebras Revisited

-- Induction Revisited

{- Define induction as usual -}

-- Initial algebras are inductive, again.

{- Prove initiality implies inductivity with the new definition. Perhaps show equivalence bewteen definitions of inductivity. -} {- Perhaps explicitly separate proof for ℕ and then experiment with diferent notions of fibered algebra / induction -}

-- Initial algebras are equivalent

-- ℤ as HIT: First, characterize computational behavior of sections on predecessor to justify definitional computation rule.

{- Postulate ℤ as a HIT with simple computation rules. Deduce the rest. Prove initiality -}


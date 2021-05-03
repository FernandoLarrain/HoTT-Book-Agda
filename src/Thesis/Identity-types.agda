{-# OPTIONS --without-K --exact-split --safe #-}

open import Ch1.Type-theory
open import Ch2.Homotopy-type-theory
open import Ch3.Sets-and-logic
open import Ch4.Equivalences
open import Thesis.Z-Algebras

module Thesis.Identity-types where


-- III. Identity Type of Sections and Morphisms

SecId : (A : Alg 𝓤) (E : FibAlg 𝓥 A) → AlgSec A E → AlgSec A E → 𝓤 ⊔ 𝓥 ̇
SecId (A , a₀ , s , i) (E , e₀ , s' , j) (f , f₀ , f-s) (g , g₀ , g-s) = Σ H ꞉ (f ∼ g) , (H a₀ ≡ f₀ ∙ g₀ ⁻¹) × ((a : A) → H (s a) ≡ f-s a ∙ ap (s' a) (H a) ∙ g-s a ⁻¹)

Sec-≡-elim : (A : Alg 𝓤) (E : FibAlg 𝓥 A) (f g : AlgSec A E) → f ≡ g → SecId A E f g
Sec-≡-elim A E f .f (refl .f) = hrefl _ , (rinv _ ⁻¹) , λ a → rinv _ ⁻¹ ∙ (ru _ ∙ᵣ _)

module _ ⦃ fe : FunExt ⦄ where

  TotSecId-is-Contr : (A : Alg 𝓤) (E : FibAlg 𝓥 A) (f : AlgSec A E) → isContr (Σ g ꞉ AlgSec A E , SecId A E f g)
  TotSecId-is-Contr {𝓤} {𝓥} (A , a₀ , s , i) (E , e₀ , s' , j) (f , f₀ , f-s) = ≃-preserves-Contr aux-equiv (≃-preserves-Contr (≃-sym (Σ-over-Contr-base-is-fib _ _ Tot-fun-is-Contr)) (×-preserves-Contr _ _ Tot-path-is-Contr Tot-htpy-is-Contr)) where

    A' = (A , a₀ , s , i)
    E' = (E , e₀ , s' , j)
    f' = (f , f₀ , f-s)

    Tot-fun : 𝓤 ⊔ 𝓥 ̇
    Tot-fun = Σ g ꞉ ((a : A) → E a) , f ∼ g

    Tot-fun-is-Contr : isContr (Tot-fun)
    Tot-fun-is-Contr = ≃-preserves-Contr (Σ-preserves-family-≃ (λ g → happly , happly-is-equiv)) (free-right-endpt-is-Contr _ _)

    Tot-path : Tot-fun → 𝓥 ̇
    Tot-path (g , H) = Σ g₀ ꞉ (g a₀ ≡ e₀) , H a₀ ≡ f₀ ∙ g₀ ⁻¹

    Tot-path-is-Contr : isContr (Tot-path (f , hrefl f))
    Tot-path-is-Contr = ≃-preserves-Contr (Σ-preserves-family-≃ aux-equiv) (free-left-endpt-is-Contr _ _) where
      aux-equiv : (g₀ : f a₀ ≡ e₀) → (g₀ ≡ f₀) ≃ (hrefl f a₀ ≡ f₀ ∙ g₀ ⁻¹) 
      aux-equiv (refl .(f a₀)) = post-∙-≃ _ (ru _)

    Tot-htpy : Tot-fun → 𝓤 ⊔ 𝓥 ̇
    Tot-htpy (g , H) = Σ g-s ꞉ ((a : A) → g (s a) ≡ s' a (g a)) , ((a : A) → H (s a) ≡ f-s a ∙ ap (s' a) (H a) ∙ g-s a ⁻¹)

    Tot-htpy-is-Contr : isContr (Tot-htpy (f , hrefl f))
    Tot-htpy-is-Contr = ≃-preserves-Contr (split , (dep-Σ-UMP A (λ a → f (s a) ≡ s' a (f a)) λ a x → refl _ ≡ f-s a ∙ refl _ ∙ x ⁻¹)) (Π-preserves-Contr _ (λ a → ≃-preserves-Contr (Σ-preserves-family-≃ (λ x → (post-∙-≃ _ (ru _ ∙ ru _ ∙ (_ ∙ₗ linv _ ⁻¹) ∙ ∙-assoc _ _ _)) ● (≃-sym (pre-∙-≃ _ (lu _))) ● ∙ᵣ-≃ _ _ x)) (free-left-endpt-is-Contr _ _)))

    aux-equiv : (Σ w ꞉ Tot-fun , Tot-path w × Tot-htpy w) ≃ (Σ g' ꞉ AlgSec A' E' , SecId A' E' f' g')
    aux-equiv = ψ , qinv-to-isequiv (ϕ , hrefl _ , hrefl _) where
      ϕ : (Σ g' ꞉ AlgSec A' E' , SecId A' E' f' g') → (Σ w ꞉ Tot-fun , Tot-path w × Tot-htpy w)
      ϕ ((g , g₀ , g-s) , (H , H₀ , H-s)) = (g , H) , (g₀ , H₀) , (g-s , H-s)
      ψ : (Σ w ꞉ Tot-fun , Tot-path w × Tot-htpy w) → (Σ g' ꞉ AlgSec A' E' , SecId A' E' f' g')
      ψ ((g , H) , (g₀ , H₀) , (g-s , H-s)) = ((g , g₀ , g-s) , (H , H₀ , H-s))

  IdSec-≃-SecId : (A : Alg 𝓤) (E : FibAlg 𝓥 A) (f g : AlgSec A E) → (f ≡ g) ≃ SecId A E f g
  IdSec-≃-SecId {𝓤} A E f g = Sec-≡-elim A E f g , pr₂ (fiberwise-≃-iff-total-≃.Hae (Sec-≡-elim A E f)) (map-between-Contrs-is-equiv _ (free-right-endpt-is-Contr _ _) (TotSecId-is-Contr A E f)) g

  Sec-≡-intro : (A : Alg 𝓤) (E : FibAlg 𝓥 A) (f g : AlgSec A E) → SecId A E f g → f ≡ g
  Sec-≡-intro A E f g = inv (IdSec-≃-SecId A E f g)

  HomId : (A : Alg 𝓤) (B : Alg 𝓥) → Hom A B → Hom A B → 𝓤 ⊔ 𝓥 ̇
  HomId (A , a₀ , s , i) (B , b₀ , s' , j) (f , f₀ , f-s) (g , g₀ , g-s) = Σ H ꞉ (f ∼ g) , (H a₀ ≡ f₀ ∙ g₀ ⁻¹) × ((a : A) → H (s a) ≡ f-s a ∙ ap s' (H a) ∙ g-s a ⁻¹)

  IdHom-≃-HomId : (A : Alg 𝓤) (B : Alg 𝓥) (f g : Hom A B) → (f ≡ g) ≃ HomId A B f g
  IdHom-≃-HomId A B = IdSec-≃-SecId A (ConstFibAlg A B)

  Hom-≡-intro : (A : Alg 𝓤) (B : Alg 𝓥) (f g : Hom A B) → HomId A B f g → f ≡ g
  Hom-≡-intro A B f g = inv (IdHom-≃-HomId A B f g)

  Hom-≡-elim : (A : Alg 𝓤) (B : Alg 𝓥) (f g : Hom A B) → f ≡ g → HomId A B f g
  Hom-≡-elim A B f g = pr₁ (IdHom-≃-HomId A B f g)  

  -- Sections are sections 

  Sec-to-Hom-gives-section : (A : Alg 𝓤) (E : FibAlg 𝓥 A) (f : AlgSec A E) → comp A (TotAlg A E) A (π₁ A E) (Sec-to-Hom A E f) ≡ algid A
  Sec-to-Hom-gives-section (A , a₀ , s , i) (E , e₀ , s' , j) (f , f₀ , f-s) = Hom-≡-intro (A , a₀ , s , i) (A , a₀ , s , i) _ _ (
    hrefl _ ,
    (dpr₁-≡-β (refl a₀) f₀ ⁻¹ ∙ ru _ ∙ ru _) ,
    λ a → dpr₁-≡-β (refl (s a)) (f-s a) ⁻¹ ∙ ru _ ∙ ru _ ∙ ru _
    )


-- IV. Associativity and Unit Laws for Morphism Composition

associator : ⦃ fe : FunExt ⦄ (A : Alg 𝓤) (B : Alg 𝓥) (C : Alg 𝓦) (D : Alg 𝓣) (f : Hom A B) (g : Hom B C) (h : Hom C D) → comp A C D h (comp A B C g f) ≡ comp A B D (comp B C D h g) f -- h (g f) ≡ (h g) f
associator (A , a₀ , sA , iA) (B , b₀ , sB , iB) (C , c₀ , sC , iC)  (D , d₀ , sD , iD) (f , f₀ , f-s) (g , g₀ , g-s) (h , h₀ , h-s) = Hom-≡-intro A' D' (comp A'  C' D' h' (comp A' B' C' g' f')) (comp A' B' D' (comp B' C' D' h' g') f') (hrefl _ , H₀ f₀ g₀ h₀ , H-s)
  where
  A' = (A , a₀ , sA , iA)
  B' = (B , b₀ , sB , iB)
  C' = (C , c₀ , sC , iC)
  D' = (D , d₀ , sD , iD)
  f' = (f , f₀ , f-s)
  g' = (g , g₀ , g-s)
  h' = (h , h₀ , h-s)
  H₀ : (f₀ : f a₀ ≡ b₀) (g₀ : g b₀ ≡ c₀) (h₀ : h c₀ ≡ d₀) → refl _ ≡ ap h (ap g f₀ ∙ g₀) ∙ h₀ ∙ ((ap (h ∘ g) f₀ ∙ (ap h g₀ ∙ h₀)) ⁻¹)
  H₀ (refl .(f a₀)) (refl .(g (f a₀))) (refl .(h (g (f a₀)))) = refl _
  H-s : (a : A) → refl _ ≡  (ap h (ap g (f-s a) ∙ g-s (f a)) ∙ h-s (g (f a)) ∙ refl _  ∙ (ap (h ∘ g) (f-s a) ∙ (ap h (g-s (f a)) ∙ h-s (g (f a)))) ⁻¹)
  H-s a = aux (f-s a) (g-s (f a)) (h-s (g (f a)))
    where
    aux : {b₁ b₂ : B} {c : C} {d : D} (f-sa : b₁ ≡ b₂) (g-sfa : _ ≡ c) (h-sgfa : _ ≡ d) → refl _ ≡  (ap h (ap g f-sa ∙ g-sfa) ∙ h-sgfa ∙ refl _  ∙ (ap (h ∘ g) f-sa ∙ (ap h g-sfa ∙ h-sgfa)) ⁻¹)
    aux (refl _) (refl .(g _)) (refl .(h (g _))) = refl _

left-unitor : ⦃ fe : FunExt ⦄ (A : Alg 𝓤) (B : Alg 𝓥) (f : Hom A B) → comp A B B (algid B) f ≡ f
left-unitor (A , a₀ , s , i) (B , .(f a₀) , s' , j) (f , refl .(f a₀) , f-s) = Hom-≡-intro A' B' (comp A' B' B' (algid B') f') f' (hrefl _ , refl _ , H-s)
  where
  A' = (A , a₀ , s , i)
  B' = (B , (f a₀) , s' , j)
  f' = (f , refl (f a₀) , f-s)
  H-s : (a : A) → refl _ ≡ ap id (f-s a) ∙ refl _ ∙ refl _ ∙ f-s a ⁻¹
  H-s a = aux (f-s a)
    where
    aux : {x y : B} (p : x ≡ y) → refl _ ≡ ap id p ∙ refl _ ∙ refl _ ∙ p ⁻¹
    aux (refl _) = refl _

right-unitor : ⦃ fe : FunExt ⦄ (A : Alg 𝓤) (B : Alg 𝓥) (f : Hom A B) → comp A A B f (algid A) ≡ f
right-unitor (A , a₀ , s , i) (B , .(f a₀) , s' , j) (f , refl .(f a₀) , f-s) = Hom-≡-intro A' B' (comp A' A' B' f' (algid A')) f' (hrefl _ , refl _ , H-s)
  where
  A' = (A , a₀ , s , i)
  B' = (B , (f a₀) , s' , j)
  f' = (f , refl (f a₀) , f-s)
  H-s : (a : A) → refl _ ≡ refl _ ∙ f-s a ∙ refl _ ∙ f-s a ⁻¹
  H-s a = aux (f-s a)
    where
    aux : {x y : B} (p : x ≡ y) → refl _ ≡ refl _ ∙ p ∙ refl _ ∙ p ⁻¹
    aux (refl _) = refl _

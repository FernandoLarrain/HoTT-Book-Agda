{-# OPTIONS --without-K --exact-split #-}

open import Ch1.Type-theory
open import Ch2.Homotopy-type-theory
open import Ch3.Sets-and-logic
open import Ch4.Equivalences
open import Ch5.8-Id-types-and-id-systems
open import Ch5.Exercises

module Thesis.Z-Algebras where


-- I. The Category of ℤ-Algebras

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
comp A B C (g , g₀ , g-s) (f , f₀ , f-s) = g ∘ f , (ap g f₀ ∙ g₀) , λ a → ap g (f-s a) ∙ g-s (f a)

-- Identity

algid : (A : Alg 𝓤) → Hom A A
algid A = id , refl _ , hrefl _


-- II. Fibered ℤ-Algebras and their Sections

-- Fibered Algebras

FibAlgStr : (A : Alg 𝓤) → (pr₁ A → 𝓥 ̇) → 𝓤 ⊔ 𝓥 ̇
FibAlgStr (A , a₀ , s , i) E = E a₀ × (Σ s' ꞉ ((a : A) → E a → E (s a)) , ((a : A) → ishae (s' a)))

FibAlg : (𝓥 : Universe) → Alg 𝓤 → 𝓤 ⊔ 𝓥 ⁺ ̇
FibAlg 𝓥 A = Σ E ꞉ (pr₁ A → 𝓥 ̇) , FibAlgStr A E

-- Associated algebra on total space

TotAlg : (A : Alg 𝓤) → FibAlg 𝓥 A → Alg (𝓤 ⊔ 𝓥)
TotAlg (A , a₀ , s , i) (E , e₀ , s' , j) = (Σ E) , (a₀ , e₀) , total↓ E s s' , pr₂ (Σ-preserves-≃ E E (s , i) (λ a → s' a , j a))

-- Projection of associated algebra is a morphism

π₁ : (A : Alg 𝓤) (E : FibAlg 𝓥 A) → Hom (TotAlg A E) A
π₁ (A , a₀ , s , i) (E , e₀ , s' , j) = pr₁ , refl a₀ , hrefl (s ∘ pr₁)

-- Fibered algebra sections

AlgSecStr : (A : Alg 𝓤) (E : FibAlg 𝓥 A) → ((a : pr₁ A) → (pr₁ E) a) → 𝓤 ⊔ 𝓥 ̇
AlgSecStr (A , a₀ , s , i) (E , e₀ , s' , j) f = (f a₀ ≡ e₀) × ((a : A) → f (s a) ≡ s' a (f a))

AlgSec : (A : Alg 𝓤) → FibAlg 𝓥 A → 𝓤 ⊔ 𝓥 ̇
AlgSec A E = Σ f ꞉ Π (pr₁ E) , AlgSecStr A E f 

-- Section induces morphism into associated algebra

Sec-to-Hom : (A : Alg 𝓤) (E : FibAlg 𝓥 A) → AlgSec A E → Hom A (TotAlg A E)
Sec-to-Hom (A , a₀ , s , i) (E , e₀ , s' , j) (f , f₀ , f-s) = (λ a → a , f a) , dpair-≡ (refl a₀ , f₀) , λ a → dpair-≡ (refl (s a) , f-s a)

-- Fibered algebra induced by a constant algebra

ConstFibAlg : (A : Alg 𝓤) (B : Alg 𝓥) → FibAlg 𝓥 A
ConstFibAlg {𝓤} {𝓥} (A , a₀ , s , i) (B , b₀ , s'  , j) = (λ a → B) , b₀ , (λ a b → s' b) , (λ a → j)

_ : (A : Alg 𝓤) (B : Alg 𝓥) → AlgSec A (ConstFibAlg A B) ≡ Hom A B
_ = λ A B → refl _


-- III. Identity Type of Sections and Morphisms

SecId : (A : Alg 𝓤) (E : FibAlg 𝓥 A) → AlgSec A E → AlgSec A E → 𝓤 ⊔ 𝓥 ̇
SecId (A , a₀ , s , i) (E , e₀ , s' , j) (f , f₀ , f-s) (g , g₀ , g-s) = Σ H ꞉ (f ∼ g) , (H a₀ ≡ f₀ ∙ g₀ ⁻¹) × ((a : A) → H (s a) ≡ f-s a ∙ ap (s' a) (H a) ∙ g-s a ⁻¹)

Sec-≡-elim : (A : Alg 𝓤) (E : FibAlg 𝓥 A) (f g : AlgSec A E) → f ≡ g → SecId A E f g
Sec-≡-elim A E f .f (refl .f) = hrefl _ , (rinv _ ⁻¹) , λ a → rinv _ ⁻¹ ∙ (ru _ ∙ᵣ _)

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

associator : (A : Alg 𝓤) (B : Alg 𝓥) (C : Alg 𝓦) (D : Alg 𝓣) (f : Hom A B) (g : Hom B C) (h : Hom C D) → comp A C D h (comp A B C g f) ≡ comp A B D (comp B C D h g) f -- h (g f) ≡ (h g) f
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

left-unitor : (A : Alg 𝓤) (B : Alg 𝓥) (f : Hom A B) → comp A B B (algid B) f ≡ f
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

right-unitor : (A : Alg 𝓤) (B : Alg 𝓥) (f : Hom A B) → comp A A B f (algid A) ≡ f
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


-- V. Identity Type of Algebras

isiso : (A : Alg 𝓤) (B : Alg 𝓥) → Hom A B → 𝓤 ⊔ 𝓥 ̇
isiso A B f = Σ g ꞉ Hom B A , (comp B A B f g ≡ algid B) × (comp A B A g f ≡ algid A)

_≅_ : Alg 𝓤 → Alg 𝓥 → 𝓤 ⊔ 𝓥 ̇
A ≅ B = Σ f ꞉ Hom A B , isiso A B f

isiso-to-isequiv : (A : Alg 𝓤) (B : Alg 𝓥) (f : Hom A B) → isiso A B f → isequiv (pr₁ f)
isiso-to-isequiv A B f (g , qfg , qgf) with Hom-≡-elim B B _ _ qfg | Hom-≡-elim A A _ _ qgf
... | (H , H-etc) | (K , K-etc) = qinv-to-isequiv (pr₁ g , H , K)

AlgId : Alg 𝓤 → Alg 𝓥 → 𝓤 ⊔ 𝓥 ̇
AlgId (A , Str-A) (B , Str-B) = Σ e ꞉ A ≃ B , HomStr (A , Str-A) (B , Str-B) (pr₁ e)
 
IdAlg-≃-AlgId : (A B : Alg 𝓤) → (A ≡ B) ≃ (AlgId A B)
IdAlg-≃-AlgId {𝓤} (A , a₀ , s , i) (B , b₀ , s' , j) = Σ-≡-≃ ● Σ-preserves-≃ _ _ (idtoeqv , idtoeqv-is-equiv {𝓤}) (aux-equiv A' B') where
  A' = (A , a₀ , s , i)
  B' = (B , b₀ , s' , j)
  aux-equiv : (A B : Alg 𝓤) (p : pr₁ A ≡ pr₁ B) → (transport AlgStr p (pr₂ A) ≡ pr₂ B) ≃ HomStr A B (coe p)
  aux-equiv (A , a₀ , s , i) (.A , b₀ , s' , j) (refl .A) = ((a₀ , s , i) ≡ (b₀ , s' , j)) ≃⟨ ×-≡-≃ ● ×-preserves-≃ (≃-refl _) (Σ-over-predicate' (ishae-is-Prop) _ _ ● happly , happly-is-equiv {𝓤}) ⟩ ((a₀ ≡ b₀) × (s ∼ s')) ■  

≅-to-≡ : (A B : Alg 𝓤) → A ≅ B → A ≡ B
≅-to-≡ A B ((f , Str-f) , i) = inv (IdAlg-≃-AlgId A B) ((f , isiso-to-isequiv A B (f , Str-f) i) , Str-f)

≡-to-≅ : (A B : Alg 𝓤) → A ≡ B → A ≅ B
≡-to-≅ A .A (refl .A) = (id , refl _ , hrefl _) , ((id , refl _ , hrefl _) , ((refl _) , (refl _)))


-- VI. Inductive Algebras

isind : (𝓥 : Universe) → Alg 𝓤 → 𝓤 ⊔ 𝓥 ⁺ ̇
isind 𝓥 A = (E : FibAlg 𝓥 A) → AlgSec A E

-- Dependent equalizer.

depEqz : (A : Alg 𝓤) (E : FibAlg 𝓤 A) → AlgSec A E → AlgSec A E → FibAlg 𝓤 A
depEqz {𝓤} (A , a₀ , s , p , σ , ρ , τ) (E , e₀ , s' , j) (f , f₀ , f-s) (g , g₀ , g-s) = Q , q₀ , t , k
  where
  i : isequiv s
  i = (p , σ , ρ , τ)
  p' : ((a : A) → E (s a) → E a)
  p' a = ishae₁ (j a)
  σ' : ((a : A) → (p' a) ∘ (s' a) ∼ id)
  σ' a = ishae₂ (j a)
  ρ' : ((a : A) → (s' a) ∘ (p' a) ∼ id)
  ρ' a = ishae₃ (j a)
  τ' : (a : A) (u : E a) → ap (s' a) (σ' a u) ≡ (ρ' a) (s' a u)
  τ' a = ishae₄ (j a)
  A' : Alg 𝓤
  A' = (A , a₀ , s , i)
  E' : FibAlg 𝓤 A'
  E' = (E , e₀ , s' , j)
  f' g' : AlgSec A' E'
  f' = (f , f₀ , f-s)
  g' = (g , g₀ , g-s)
  Q : A → 𝓤 ̇
  Q a = f a ≡ g a
  q₀ : Q a₀
  q₀ = f₀ ∙ g₀ ⁻¹  
  t : (a : A) → Q a → Q (s a)
  t a q = f-s a ∙ ap (s' a) q ∙ g-s a ⁻¹
  tinv : (a : A) → Q (s a) → Q a
  tinv a q = σ' a (f a) ⁻¹ ∙ ap (p' a) (f-s a ⁻¹ ∙ q ∙ g-s a) ∙ σ' a (g a)
  α : (a : A) → t a ∘ tinv a ∼ id
  α a q = ap (λ - → f-s a ∙ - ∙ g-s a ⁻¹) (ap-∙ (s' a) _ _ ∙ ((ap-∙ (s' a) _ _ ∙ ((ap-⁻¹ (s' a) _ ∙ ap _⁻¹ (τ' a (f a))) ∙ᵣ ap (s' a) _)) ✦ τ' a (g a))) ∙ aux (s' a) (p' a) (ρ' a) (f-s a) (g-s a) q where
    aux : {A : 𝓤 ̇} {B : 𝓥 ̇} (f : A → B) (g : B → A) (H : f ∘ g ∼ id) {b₁ b₁' b₂ b₂' : B} (p₁ : b₁ ≡ b₁') (p₂ : b₂ ≡ b₂') (q : b₁ ≡ b₂) → p₁ ∙ (H _ ⁻¹ ∙ ap f (ap g (p₁ ⁻¹ ∙ q ∙ p₂)) ∙ H _) ∙ p₂ ⁻¹ ≡ q
    aux f g H (refl _) (refl _) (refl _) = ru _ ⁻¹ ∙ lu _ ⁻¹ ∙ ((ru _ ⁻¹ ∙ᵣ H _) ∙ linv _)
  β : (a : A) → tinv a ∘ t a ∼ id
  β a q = aux (s' a) (p' a) (σ' a) (f-s a) (g-s a) q where
    aux : {A : 𝓤 ̇} {B : 𝓥 ̇} (f : A → B) (g : B → A) (H : g ∘ f ∼ id) {x y : A} {b₁ b₂ : B} (p₁ : b₁ ≡ _) (p₂ : b₂ ≡ _) (q : x ≡ y) → H x ⁻¹ ∙ ap g (p₁ ⁻¹ ∙ (p₁ ∙ ap f q ∙ p₂ ⁻¹) ∙ p₂) ∙ H y ≡ q
    aux f g H (refl .(f _)) (refl .(f _)) (refl _) = (ru _ ⁻¹ ∙ᵣ H _) ∙ linv _
  k : (a : A) → ishae (t a)
  k a = qinv-to-isequiv (tinv a , α a , β a)

uniqueness-pple : (A : Alg 𝓤) → isind 𝓤 A → (E : FibAlg 𝓤 A) → isProp (AlgSec A E)
uniqueness-pple A A-ind E f g = Sec-≡-intro A E f g (A-ind (depEqz A E f g))

isind-is-Prop : (A : Alg 𝓤) → isProp (isind 𝓤 A)
isind-is-Prop {𝓤} A A-ind = aux A-ind
  where
  aux : isProp (isind 𝓤 A)
  aux = Π-preserves-Props _ (λ E → uniqueness-pple A A-ind E)


-- VII. Initial Algebras

ishinit : (𝓥 : Universe) → Alg 𝓤 → 𝓤 ⊔ 𝓥 ⁺ ̇
ishinit 𝓥 A = (B : Alg 𝓥) → isContr (Hom A B)

ishinit-is-Prop : (𝓥 : Universe) (A : Alg 𝓤) → isProp (ishinit 𝓥 A)
ishinit-is-Prop 𝓥 A = Π-preserves-Props _ (λ B → isContr-is-Prop _)

hasrec : (𝓥 : Universe) → Alg 𝓤 → 𝓤 ⊔ 𝓥 ⁺ ̇
hasrec 𝓥 A = (B : Alg 𝓥) → Hom A B

hasrecunique : (𝓥 : Universe) (A : Alg 𝓤) → 𝓤 ⊔ 𝓥 ⁺ ̇
hasrecunique 𝓥 A = (B : Alg 𝓥) → isProp (Hom A B)

ishinit-is-rec&unique : (𝓥 : Universe) (A : Alg 𝓤) → ishinit 𝓥 A ≃ (hasrec 𝓥 A × hasrecunique 𝓥 A) 
ishinit-is-rec&unique {𝓤} 𝓥 A = ⇔-to-≃ (ishinit-is-Prop 𝓥 A) rec&unique-is-Prop (ishinit-to-rec&unique , rec&unique-to-ishinit)
  where
  rec&unique-is-Prop : isProp (hasrec 𝓥 A × hasrecunique 𝓥 A)
  rec&unique-is-Prop (rec , η) (rec' , η') = inv ×-≡-≃ ((funext (λ B → η B _ _)) , Π-preserves-Props _ (λ B → isProp-is-Prop _) _ _)
  ishinit-to-rec&unique : ishinit 𝓥 A → hasrec 𝓥 A × hasrecunique 𝓥 A
  ishinit-to-rec&unique A-init = (λ B → pr₁ (A-init B)) , (λ B → isContr-to-isProp (A-init B))
  rec&unique-to-ishinit : hasrec 𝓥 A × hasrecunique 𝓥 A → ishinit 𝓥 A
  rec&unique-to-ishinit (rec , η) B = (rec B) , (η B (rec B))

rec&unique-to-ishinit : (𝓥 : Universe) (A : Alg 𝓤) → hasrec 𝓥 A × hasrecunique 𝓥 A → ishinit 𝓥 A
rec&unique-to-ishinit 𝓥 A = inv (ishinit-is-rec&unique 𝓥 A) 

InitAlg : (𝓤 : Universe) → 𝓤 ⁺ ̇
InitAlg 𝓤 = Σ A ꞉ Alg 𝓤 , ishinit 𝓤 A

InitAlg-is-Prop : (𝓤 : Universe) → isProp (InitAlg 𝓤)
InitAlg-is-Prop 𝓤 (A , A-init) (B , B-init)  = Σ-over-predicate (ishinit-is-Prop 𝓤) (≅-to-≡ A B (
  pr₁ (A-init B) ,
  pr₁ (B-init A) ,
  isContr-to-isProp (B-init B) _ _ ,
  isContr-to-isProp (A-init A) _ _
  ))

≅-is-Contr : (A B : InitAlg 𝓤) → isContr (pr₁ A ≅ pr₁ B)
≅-is-Contr (A , A-init) (B , B-init) = ≃-preserves-Contr (≃-sym (Σ-over-Contr-base-is-fib (Hom A B) (isiso A B) (A-init B) ● Σ-over-Contr-base-is-fib (Hom B A) _ (B-init A))) (×-preserves-Contr _ _ (pr₁ Prop-iff-Contr-≡ (pr₂ (pr₁ isContr-iff-is-inhabited-Prop (B-init B))) _ _) (pr₁ Prop-iff-Contr-≡ (pr₂ (pr₁ isContr-iff-is-inhabited-Prop (A-init A))) _ _))


-- VIII. Every Inductive Algebra is Initial

isind-to-hasrec : (A : Alg 𝓤) → isind 𝓤 A → hasrec 𝓤 A
isind-to-hasrec A A-ind B = A-ind (ConstFibAlg A B)

isind-to-hasrecunique : (A : Alg 𝓤) → isind 𝓤 A → hasrecunique 𝓤 A
isind-to-hasrecunique {𝓤} A A-ind B = uniqueness-pple A A-ind (ConstFibAlg A B)

isind-to-ishinit : (A : Alg 𝓤) → isind 𝓤 A → ishinit 𝓤 A
isind-to-ishinit A A-ind B = pr₂ isContr-iff-is-inhabited-Prop (isind-to-hasrec A A-ind B , isind-to-hasrecunique A A-ind B)


-- IX. Every Initial Algebra is Inductive

ishinit-to-isind : (A : Alg 𝓤) → ishinit 𝓤 A → isind 𝓤 A
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

  path : (f₁ , f₀₁ , f-s₁) ≡ algid A'
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

isind-iff-ishinit : (A : Alg 𝓤) → isind 𝓤 A ⇔ ishinit 𝓤 A
isind-iff-ishinit A = (isind-to-ishinit A) , (ishinit-to-isind A)

isind-≃-ishinit : (A : Alg 𝓤) → isind 𝓤 A ≃ ishinit 𝓤 A
isind-≃-ishinit {𝓤} A = ⇔-to-≃ (isind-is-Prop A) (ishinit-is-Prop 𝓤 A) (isind-iff-ishinit A)


-- X. Preservation of Equivalences

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

  module _ (f-s : s-pres) (f-p : p-pres) where

    f-σ-top : f₁ ∘ p ∘ s ∼ p' ∘ s' ∘ f₁
    f-σ-top a₁ = f-p (s a₁) ∙ ap p' (f-s a₁)

    σ-pres : 𝓤 ⊔ 𝓥 ̇
    σ-pres = (a₁ : A₁) → ap f₁ (σ a₁) ≡ f-σ-top a₁ ∙ σ' (f₁ a₁)

    f-ρ-top : f₂ ∘ s ∘ p ∼ s' ∘ p' ∘ f₂
    f-ρ-top a₂ = f-s (p a₂) ∙ ap s' (f-p a₂)

    ρ-pres : 𝓤 ⊔ 𝓥 ̇
    ρ-pres = (a₂ : A₂) → ap f₂ (ρ a₂) ≡ f-ρ-top a₂ ∙ ρ' (f₂ a₂)

    f-τ-top : f₂ ∘ s ∘ p ∘ s ∼ s' ∘ p' ∘ s' ∘ f₁
    f-τ-top a₁ = f-ρ-top (s a₁) ∙ ap s' (ap p' (f-s a₁))

    module _ (f-σ : σ-pres) (f-ρ : ρ-pres) where

      front : (a₁ : A₁) → ap f₂ (ap s (σ a₁)) ∙ f-s a₁ ≡ f-τ-top a₁ ∙ ap s' (σ' (f₁ a₁))
      front a₁ = (ap-∘ s f₂ (σ a₁) ∙ᵣ f-s a₁) ∙ hnat f-s (σ a₁) ⁻¹ ∙ (f-s (p (s a₁)) ∙ₗ (ap-∘ f₁ s' (σ a₁) ⁻¹ ∙ ap (ap s') (f-σ a₁) ∙ ap-∙ s' _ _)) ∙ ∙-assoc _ _ _ ∙ (((f-s (p (s a₁)) ∙ₗ ap-∙ s' _ _) ∙ ∙-assoc _ _ _) ∙ᵣ ap s' (σ' (f₁ a₁)))

      back : (a₁ : A₁) → ap f₂ (ρ (s a₁)) ∙ f-s a₁ ≡ f-τ-top a₁ ∙ ρ' (s' (f₁ a₁))
      back a₁ = (f-ρ (s a₁) ✦ ap-id (f-s a₁) ⁻¹) ∙ ∙-assoc _ _ _ ⁻¹ ∙ (f-ρ-top (s a₁) ∙ₗ (hnat ρ' (f-s a₁) ∙ (ap-∘ p' s' (f-s a₁) ⁻¹ ∙ᵣ ρ' (s' (f₁ a₁))))) ∙ ∙-assoc _ _ _

      τ-pres : 𝓤 ⊔ 𝓥 ̇
      τ-pres = (a₁ : A₁) → (ap (ap f₂) (τ a₁) ∙ᵣ f-s a₁) ∙ back a₁ ≡ front a₁ ∙ (f-τ-top a₁ ∙ₗ τ' (f₁ a₁))

  ishae-pres : (f-s : s-pres) → 𝓤 ⊔ 𝓥 ̇
  ishae-pres f-s = Σ f-p ꞉ p-pres , Σ f-σ ꞉ σ-pres f-s f-p , Σ f-ρ ꞉ ρ-pres f-s f-p , τ-pres f-s f-p f-σ f-ρ

  hae-pres : 𝓤 ⊔ 𝓥 ̇
  hae-pres = Σ f-s ꞉ s-pres , ishae-pres f-s


-- XI. Equivalence Preservation is Function Preservation

abstract

  module _ (A : 𝓤 ̇) (B : 𝓥 ̇) (f : A → B) where

    open Preservation-of-Equivalences A A (≃-refl A) B B (≃-refl B) f f 

    ishae-pres-is-Contr' : isContr (ishae-pres (hrefl _))
    ishae-pres-is-Contr' = ≃-preserves-Contr (≃-sym (Σ-assoc _ _ _ ● Σ-over-Contr-base-is-fib _ _ Contr-f-pσ)) Contr-f-ρτ where

      Contr-f-pσ : isContr (Σ f-p ꞉ p-pres , σ-pres (hrefl _) f-p)
      Contr-f-pσ = ≃-preserves-Contr
        (split , (dep-Σ-UMP A (λ a → f a ≡ f a) λ a f-pa → refl (f a) ≡ (f-pa ∙ refl (f a)) ∙ refl (f a)))
        (Π-preserves-Contr _ (λ a → ≃-preserves-Contr (Σ-preserves-family-≃ (λ f-pa → post-∙-≃ (refl (f a)) (ru f-pa ∙ ru _))) (free-right-endpt-is-Contr _ _)))  

      Contr-f-ρτ : isContr (Σ f-ρ ꞉ ρ-pres (hrefl _) (hrefl _) , τ-pres (hrefl _) (hrefl _) (hrefl _) f-ρ)
      Contr-f-ρτ = ≃-preserves-Contr
        (split , (dep-Σ-UMP A (λ a → refl (f a) ≡ refl _ ∙ refl _ ∙ refl _) λ a f-ρa → refl _ ∙ (refl _ ∙ f-ρa ∙ refl _ ∙ refl _ ∙ refl _ ∙ refl _ ∙ refl _) ≡ refl (refl (f a))))
        (Π-preserves-Contr _ (λ a → ≃-preserves-Contr (Σ-preserves-family-≃ (λ f-ρa → pre-∙-≃ (refl (refl (f a))) (lu _ ⁻¹ ∙ ru _ ⁻¹ ∙ ru _ ⁻¹ ∙ ru _ ⁻¹ ∙ ru _ ⁻¹ ∙ ru _ ⁻¹ ∙ lu f-ρa ⁻¹))) (free-left-endpt-is-Contr _ _)))

  open Preservation-of-Equivalences using (ishae-pres ; hae-pres)

  ishae-pres-is-Contr : (A₁ A₂ : 𝓤 ̇) (e : A₁ ≃ A₂) (B₁ B₂ : 𝓥 ̇) (e' : B₁ ≃ B₂) (f₁ : A₁ → B₁) (f₂ : A₂ → B₂) (f-s : f₂ ∘ pr₁ e ∼ pr₁ e' ∘ f₁) → isContr (ishae-pres A₁  A₂ e B₁ B₂ e' f₁ f₂ f-s)
  ishae-pres-is-Contr {𝓤} {𝓥} = 𝕁-≃ (λ A₁ A₂ e → (B₁ B₂ : 𝓥 ̇) (e' : B₁ ≃ B₂) (f₁ : A₁ → B₁) (f₂ : A₂ → B₂) (f-s : f₂ ∘ pr₁ e ∼ pr₁ e' ∘ f₁) → isContr (ishae-pres A₁ A₂ e B₁ B₂ e' f₁ f₂ f-s)) λ A →
    𝕁-≃ (λ B₁ B₂ e' → (f₁ : A → B₁) (f₂ : A → B₂) (f-s : f₂ ∘ id ∼ pr₁ e' ∘ f₁) → isContr (ishae-pres A A (≃-refl A) B₁ B₂ e' f₁ f₂ f-s)) λ B f₁ f₂ →
      𝕁-∼ (λ f₂ f₁ f-s → isContr (ishae-pres A A (≃-refl A) B B (≃-refl B) f₁ f₂ f-s)) (λ f → ishae-pres-is-Contr' A B f) f₂ f₁

hae-pres-≃-fun-pres : (A₁ A₂ : 𝓤 ̇) (e : A₁ ≃ A₂) (B₁ B₂ : 𝓥 ̇) (e' : B₁ ≃ B₂) (f₁ : A₁ → B₁) (f₂ : A₂ → B₂) → hae-pres A₁ A₂ e B₁ B₂ e' f₁ f₂ ≃ (f₂ ∘ pr₁ e ∼ pr₁ e' ∘ f₁)
hae-pres-≃-fun-pres A₁ A₂ e B₁ B₂ e' f₁ f₂ = Σ-of-Contr-family-is-base _ _ (ishae-pres-is-Contr A₁ A₂ e B₁ B₂ e' f₁ f₂)

fun-pres-to-hae-pres : {A₁ A₂ : 𝓤 ̇} (e : A₁ ≃ A₂) {B₁ B₂ : 𝓥 ̇} (e' : B₁ ≃ B₂) (f₁ : A₁ → B₁) (f₂ : A₂ → B₂) → (f₂ ∘ pr₁ e ∼ pr₁ e' ∘ f₁) → hae-pres A₁ A₂ e B₁ B₂ e' f₁ f₂
fun-pres-to-hae-pres {𝓤} {𝓥} {A₁} {A₂} e {B₁} {B₂} e' f₁ f₂ = inv (hae-pres-≃-fun-pres A₁ A₂ e B₁ B₂ e' f₁ f₂)


-- XI. Slice over an algebra.

Slice : (𝓥 : Universe) → Alg 𝓤 → 𝓤 ⊔ (𝓥 ⁺) ̇
Slice {𝓤} 𝓥 A = Σ B ꞉ Alg 𝓥 , Hom B A

Slice-is-FibAlg : (A : Alg 𝓤) → Slice 𝓤 A ≃ FibAlg 𝓤 A
Slice-is-FibAlg {𝓤} (A , a₀ , s , i) =
  Slice 𝓤 A'
    ≃⟨ lemma1 ⟩
  Slice'
    ≃⟨ Σ-preserves-≃' _ _ (thm-4-8-3.χ _ , thm-4-8-3.χ-is-equiv _) (λ E → ×-preserves-≃ (fibs-of-pr₁-are-values a₀) (lemma2 (s , i) E E))  ⟩
  FibAlg 𝓤 A' ■
  
  where
  
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

AlgSec-is-Sec : (A : Alg 𝓤) (E : FibAlg 𝓤 A) → AlgSec A E ≃ (Σ f ꞉ (Hom A (TotAlg A E)) , comp A (TotAlg A E) A (π₁ A E) f ≡ algid A)
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


-- XIII. Finite Limits

_⨂_ : Alg 𝓤 → Alg 𝓤 → Alg 𝓤
(A , a₀ , (s , p , σ , ρ , τ)) ⨂ (B , b₀ , (s' , p' , σ' , ρ' , τ')) = (A × B) , (a₀ , b₀) , ((Σ-induction (λ a b → s a , s' b)) , qinv-to-isequiv ((Σ-induction (λ a b → p a , p' b)) , (Σ-induction λ a b → pair-≡ (ρ a , ρ' b)) , (Σ-induction λ a b → pair-≡ (σ a , σ' b))))

proj₁ : (A B : Alg 𝓤) → Hom (A ⨂ B) A
proj₁ A B = pr₁ , ((refl _) , (hrefl _))

proj₂ : (A B : Alg 𝓤) → Hom (A ⨂ B) B
proj₂ A B = pr₂ , ((refl _) , (hrefl _))

⨂-UMP : (A B C : Alg 𝓤) → Hom C (A ⨂ B) ≃ Hom C A × Hom C B
⨂-UMP {𝓤} A B C = ϕ , qinv-to-isequiv (ψ , ϕ∘ψ , ψ∘ϕ) where
  ϕ : Hom C (A ⨂ B) → Hom C A × Hom C B
  ϕ f = comp C (A ⨂ B) A (proj₁ A B) f , comp C (A ⨂ B) B (proj₂ A B) f
  ψ : Hom C A × Hom C B → Hom C (A ⨂ B)
  ψ ((g , g₀ , g-s) , (h , h₀ , h-s)) = (λ c → g c , h c) , ((pair-≡ (g₀ , h₀)) , (λ c → pair-≡ (g-s c , h-s c)))
  ϕ∘ψ : ϕ ∘ ψ ∼ id
  ϕ∘ψ ((g , g₀ , g-s) , (h , h₀ , h-s)) = pair-≡ (Hom-≡-intro C A _ _ ((hrefl _) , (rinv g₀ ⁻¹ ∙ (((ap-pr₁-β g₀ h₀) ⁻¹ ∙ ru _) ∙ᵣ g₀ ⁻¹)) , λ c → rinv (g-s c) ⁻¹ ∙ (((ap-pr₁-β (g-s c) (h-s c)) ⁻¹ ∙ ru _ ∙ ru _) ∙ᵣ g-s c ⁻¹)) , Hom-≡-intro C B _ _ ((hrefl _) , (rinv h₀ ⁻¹ ∙ (((ap-pr₂-β g₀ h₀) ⁻¹ ∙ ru _) ∙ᵣ h₀ ⁻¹)) , λ c → rinv (h-s c) ⁻¹ ∙ (((ap-pr₂-β (g-s c) (h-s c)) ⁻¹ ∙ ru _ ∙ ru _) ∙ᵣ h-s c ⁻¹)))
  ψ∘ϕ : ψ ∘ ϕ ∼ id
  ψ∘ϕ (f , f₀ , f-s) = dpair-≡ ((refl _) , (pair-≡ ((ap (λ - → pair-≡ (- , (ap pr₂ f₀ ∙ refl _))) (ru _ ⁻¹) ∙ (ap (λ - → pair-≡ (ap pr₁ f₀ , -)) (ru _ ⁻¹) ∙ pr-≡-η _)) , funext (λ c → ap (λ - → pair-≡ (- , (ap pr₂ (f-s c) ∙ refl _))) (ru _ ⁻¹) ∙ (ap (λ - → pair-≡ (ap pr₁ (f-s c) , -)) (ru _ ⁻¹) ∙ pr-≡-η _)))))

Eqz : (A B : Alg 𝓤) → Hom A B → Hom A B → Alg 𝓤
Eqz A B f g = TotAlg A (depEqz A (ConstFibAlg A B) f g)

Eqz-map : (A B : Alg 𝓤) (f g : Hom A B) → Hom (Eqz A B f g) A
Eqz-map A B f g = pr₁ , refl _ , hrefl _

Eqz-equalizes' : (A B : Alg 𝓤) (f g : Hom A B) → HomId (Eqz A B f g) B (comp (Eqz A B f g) A B f (Eqz-map A B f g)) (comp (Eqz A B f g) A B g (Eqz-map A B f g))
Eqz-equalizes' (A , a₀ , s , i) (B , b₀ , s' , j) (f , f₀ , f-s) (g , g₀ , g-s) = (Σ-induction λ a q → q) , (((lu _ ∙ᵣ (g₀ ⁻¹)) ∙ ((refl _ ∙ f₀) ∙ₗ (ap _⁻¹ (lu _)))) , Σ-induction λ a q → ap (λ - → - ∙ ap s' q ∙ g-s a ⁻¹) (lu _) ∙ ((refl _ ∙ f-s a ∙ ap s' q) ∙ₗ ap _⁻¹ (lu _)))

Eqz-equalizes : (A B : Alg 𝓤) (f g : Hom A B) → comp (Eqz A B f g) A B f (Eqz-map A B f g) ≡ comp (Eqz A B f g) A B g (Eqz-map A B f g)
Eqz-equalizes A B f g = Hom-≡-intro (Eqz A B f g) B _ _ (Eqz-equalizes' A B f g)

Eqz-UMP : (A B C : Alg 𝓤) (f g : Hom A B) → Hom C (Eqz A B f g) ≃ (Σ h ꞉ Hom C A , comp C A B f h ≡ comp C A B g h)
Eqz-UMP {𝓤} (A , a₀ , s , i) (B , b₀ , s' , i') (C , c₀ , t , j) (f , f₀ , f-s) (g , g₀ , g-s) =
  _
    ≃⟨ lemma4 ⟩
  Regroup
    ≃⟨ ≃-sym lemma1 ⟩
  ((Σ h' ꞉ Hom C' A' , HomId C' B' (comp C' A' B' f' h') (comp C' A' B' g' h')))
    ≃⟨ Σ-preserves-family-≃ (λ h' → ≃-sym (IdHom-≃-HomId C' B' (comp C' A' B' f' h') (comp C' A' B' g' h'))) ⟩
  (Σ h' ꞉ Hom C' A' , comp C' A' B' f' h' ≡ comp C' A' B' g' h') ■
  where
  
  A' B' C' E' : Alg 𝓤
  A' = (A , a₀ , s , i)
  B' = (B , b₀ , s' , i')
  C' = (C , c₀ , t , j)
  f' g' : Hom A' B'
  f' = (f , f₀ , f-s)
  g' = (g , g₀ , g-s)
  E' = (Eqz A' B' f' g')
  E = pr₁ E'
  e₀ = pr₁ (pr₂ E')
  t' = pr₁ (pr₂ (pr₂ E'))
  j' = pr₂ (pr₂ (pr₂ E'))
  m' : Hom E' A'
  m' = Eqz-map A' B' f' g'
  m = pr₁ m'
  m₀ = pr₁ (pr₂ m')
  m-s = pr₂ (pr₂ m')
  meq' = Eqz-equalizes' A' B' f' g'
  meq = pr₁ meq'
  
  Regroup : 𝓤 ̇
  Regroup = Σ w ꞉ (Σ h ꞉ (C → A) , f ∘ h ∼ g ∘ h) , (Σ h₀ ꞉ (pr₁ w) c₀ ≡ a₀ , (pr₂ w) c₀ ≡ ap f h₀ ∙ f₀ ∙ (ap g h₀ ∙ g₀) ⁻¹) × (Σ h-s ꞉ (pr₁ w) ∘ t ∼ s ∘ (pr₁ w) , ((c : C) → (pr₂ w) (t c) ≡ ap f (h-s c) ∙ f-s ((pr₁ w) c) ∙ ap s' ((pr₂ w) c) ∙ (ap g (h-s c) ∙ g-s ((pr₁ w) c)) ⁻¹))
  
  lemma1 : (Σ h' ꞉ Hom C' A' , HomId C' B' (comp C' A' B' f' h') (comp C' A' B' g' h')) ≃ Regroup
  lemma1 = ϕ , qinv-to-isequiv (ψ , hrefl _ , hrefl _)
    where
    ϕ : (Σ h' ꞉ Hom C' A' , HomId C' B' (comp C' A' B' f' h') (comp C' A' B' g' h')) → Regroup
    ϕ ((h , h₀ , h-s) , (q , q₀ , q-s)) = (h , q) , (h₀ , q₀) , (h-s , q-s)
    ψ : Regroup → (Σ h' ꞉ Hom C' A' , HomId C' B' (comp C' A' B' f' h') (comp C' A' B' g' h'))
    ψ ((h , q) , (h₀ , q₀) , (h-s , q-s)) = ((h , h₀ , h-s) , (q , q₀ , q-s))

  ϕ : (C → pr₁ (Eqz A' B' f' g')) → Σ h ꞉ (C → A) , f ∘ h ∼ g ∘ h  
  ϕ u = pr₁ ∘ u , meq ∘ u
  ψ : (Σ h ꞉ (C → A) , f ∘ h ∼ g ∘ h) → (C → pr₁ (Eqz A' B' f' g'))
  ψ (h , q) c = (h c) , (q c)
  ϕ∘ψ : ϕ ∘ ψ ∼ id
  ϕ∘ψ = hrefl _
  ψ∘ϕ : ψ ∘ ϕ ∼ id
  ψ∘ϕ = hrefl _

  lemma2 : (a : A) (p : f a ≡ g a) (h₀ : a ≡ a₀) → (transport (λ - → f - ≡ g -) h₀ p ≡ f₀ ∙ g₀ ⁻¹) ≃ (p ≡ (ap f h₀ ∙ f₀ ∙ (ap g h₀ ∙ g₀) ⁻¹))
  lemma2 a p (refl .a) = post-∙-≃ p (ap (λ - → f₀ ∙ - ⁻¹) (lu g₀) ∙ lu _ ∙ ∙-assoc _ _ _)

  lemma3 : {b₀ b₁ b₂ b₃ b₄ b₅ : B} (p₁ : b₀ ≡ b₁) (p₂ : _ ≡ b₂) (p₃ : _ ≡ b₃) (p₄ : _ ≡ b₄) (p₅ : _ ≡ b₅) (p₆ : _ ≡ _) → (p₁ ⁻¹ ∙ p₂ ∙ p₃ ≡ p₄ ∙ p₅ ∙ p₆ ⁻¹) ≃ (p₂ ≡ p₁ ∙ p₄ ∙ p₅ ∙ (p₃ ∙ p₆) ⁻¹) 
  lemma3 {b₀} {.b₀} {.b₀} {.b₀} {.b₀} {.b₀} (refl .b₀) p₂ (refl .b₀) (refl .b₀) (refl .b₀) (refl .b₀) = pre-∙-≃ _ (lu _ ∙ ru _)

  lemma4 : Hom C' (Eqz A' B' f' g') ≃ Regroup
  lemma4 = Σ-preserves-≃' _ _ (ϕ , qinv-to-isequiv (ψ , hrefl _ , hrefl _)) (Σ-induction λ h q → ×-preserves-≃
      (Σ-≡-≃ ● Σ-preserves-family-≃ (λ h₀ → lemma2 (h c₀) (q c₀) h₀))
      (Π-preserves-family-≃ (λ c →
        Σ-≡-≃ ● Σ-preserves-family-≃ (λ h-sc →
          (pre-∙-≃ _ (transport-funval-≡ f g h-sc (q (t c)) ⁻¹)) ●
          lemma3 _ _ _ _ _ _)) ●
        split , (dep-Σ-UMP C _ (λ c h-sc → q (t c) ≡ ap f h-sc ∙ f-s (h c) ∙ ap s' (q c) ∙ (ap g h-sc ∙ g-s (h c)) ⁻¹))))

-- Previous equivalence is precomposition by equalizer:

Eqz-UMP-is-precomp : (A B C : Alg 𝓤) (f g : Hom A B) → pr₁ ∘ (pr₁ (Eqz-UMP A B C f g)) ∼ comp C (Eqz A B f g) A (Eqz-map A B f g)
Eqz-UMP-is-precomp {𝓤} (A , a₀ , s , i) (B , b₀ , s' , i') (C , c₀ , t , j) (f , f₀ , f-s) (g , g₀ , g-s) (u , u₀ , u-s) = dpair-≡ ((refl _) , (pair-≡ ((ap pr₁ (dpr-≡-agreement u₀) ∙ ru _) , funext (λ c → ap pr₁ (dpr-≡-agreement (u-s c)) ∙ ru _))))


-- XIV. Alternative proof of isind-≃-ishinit.

module _ (𝓤 : Universe) where

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
    (λ {A} {B} → Eqz-equalizes A B) using (thm)

  isind-≃-ishinit' : (A : Alg 𝓤) → isind 𝓤 A ≃ ishinit 𝓤 A
  isind-≃-ishinit' A =
    _
      ≃⟨ Π-preserves-≃ _ _ (≃-sym (Slice-is-FibAlg A)) (λ E → AlgSec-is-Sec A E) ⟩
    _
      ≃⟨ GCCAdj _ _ _ ⟩
    _
      ≃⟨ ≃-sym (thm A) ⟩
    _ ■


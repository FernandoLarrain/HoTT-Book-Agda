{-# OPTIONS --without-K --exact-split --rewriting #-}

open import Ch1.Type-theory
open import Ch2.Homotopy-type-theory
open import Ch3.Sets-and-logic
open import Ch4.Equivalences
open import Ch5.8-Id-types-and-id-systems
open import Rewrite

module int-as-HIT.thesis2 ⦃ fe : FunExt ⦄ ⦃ univ : Univalence ⦄ where


-- ?. The Category of ℤ-Algebras

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


-- ?. Fibered ℤ-Algebras and their Sections

-- Fibered Algebras

total↓ : {A : 𝓤 ̇} {B : 𝓥 ̇} {P : A → 𝓦 ̇} (Q : B → 𝓣 ̇) (f : A → B) → ((a : A) → P a → Q (f a)) → Σ P → Σ Q
total↓ Q f g (a , u) = f a , g a u

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


-- ?. Identity Type of Sections and Morphisms

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


-- ?. Identity Type of Algebras

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


-- ?. Inductive Algebras

isind : (𝓥 : Universe) → Alg 𝓤 → 𝓤 ⊔ 𝓥 ⁺ ̇
isind 𝓥 A = (E : FibAlg 𝓥 A) → AlgSec A E

uniqueness-pple : (A : Alg 𝓤) → isind 𝓤 A → (E : FibAlg 𝓤 A) → isProp (AlgSec A E)
uniqueness-pple {𝓤} (A , a₀ , s , p , σ , ρ , τ) A-ind (E , e₀ , s' , j) (f , f₀ , f-s) (g , g₀ , g-s) = Sec-≡-intro A' E' f' g' (A-ind Q')
  where
  i = (p , σ , ρ , τ)
  p' : ((a : A) → E (s a) → E a)
  p' a = ishae₁ (j a)
  σ' : ((a : A) → (p' a) ∘ (s' a) ∼ id)
  σ' a = ishae₂ (j a)
  ρ' : ((a : A) → (s' a) ∘ (p' a) ∼ id)
  ρ' a = ishae₃ (j a)
  τ' : (a : A) (u : E a) → ap (s' a) (σ' a u) ≡ (ρ' a) (s' a u)
  τ' a = ishae₄ (j a) 
  A' = (A , a₀ , s , i)
  E' = (E , e₀ , s' , j)
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
  Q' : FibAlg 𝓤 A'
  Q' = Q , q₀ , t , k 

isind-is-Prop : (A : Alg 𝓤) → isProp (isind 𝓤 A)
isind-is-Prop {𝓤} A A-ind = aux A-ind
  where
  aux : isProp (isind 𝓤 A)
  aux = Π-preserves-Props _ (λ E → uniqueness-pple A A-ind E)


-- ?. Initial Algebras

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


-- ?. Every Inductive Algebra is Initial

isind-to-hasrec : (A : Alg 𝓤) → isind 𝓤 A → hasrec 𝓤 A
isind-to-hasrec A A-ind B = A-ind (ConstFibAlg A B)

isind-to-hasrecunique : (A : Alg 𝓤) → isind 𝓤 A → hasrecunique 𝓤 A
isind-to-hasrecunique {𝓤} A A-ind B = uniqueness-pple A A-ind (ConstFibAlg A B)

isind-to-ishinit : (A : Alg 𝓤) → isind 𝓤 A → ishinit 𝓤 A
isind-to-ishinit A A-ind B = pr₂ isContr-iff-is-inhabited-Prop (isind-to-hasrec A A-ind B , isind-to-hasrecunique A A-ind B)


-- ?. Every Initial Algebra is Inductive

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

  -- 3. Description of composite morphism π₁∘f

  π₁∘f : Hom A' A'
  π₁∘f = comp A' T A' (π₁ A' E') A-rec

  _ : pr₁ (π₁∘f) ≡ f₁
  _ = refl _

  f₁₀ : f₁ a₀ ≡ a₀
  f₁₀ = ap pr₁ f₀ ∙ refl a₀

  _ : f₁₀ ≡ pr₁ (pr₂ π₁∘f)
  _ = refl _

  f₁-s : f₁ ∘ s ∼ s ∘ f₁
  f₁-s a = ap pr₁ (f-s a) ∙ refl _
  _ : f₁-s ≡ pr₂ (pr₂ π₁∘f)
  _ = refl _

  -- 3.1 First components of f agree with composite π₁∘f

  path-agreement : f₀₁ ≡ f₁₀
  path-agreement = ap pr₁ (dpr-≡-agreement f₀) ∙ ru _

  htpy-agreement : f-s₁ ∼ f₁-s
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

  H₀ : H a₀ ≡ f₁₀
  H₀ = pr₁ (pr₂ pathext) ∙ ru _ ⁻¹  

  H-s : (a : A) → H (s a) ≡ f₁-s a ∙ ap s (H a)
  H-s a = pr₂ (pr₂ pathext) a ∙ ru _ ⁻¹
  
  -- 5. Construction of section

  g : (a : A) → E a
  g a = transport E (H a) (f₂ a)

  g₀ : g a₀ ≡ e₀
  g₀ = transport E (H a₀) (f₂ a₀)
           ≡⟨ ap (λ - → transport E - (f₂ a₀)) H₀ ⟩
         transport E f₁₀ (f₂ a₀)
           ≡⟨ ap (λ - → transport E - (f₂ a₀)) (path-agreement ⁻¹) ⟩
         transport E f₀₁ (f₂ a₀)
           ≡⟨ f₀₂ ⟩
         e₀ ∎

  g-s : (a : A) → g (s a) ≡ s' a (g a)
  g-s a = transport E (H (s a)) (f₂ (s a))
            ≡⟨ ap (λ - → transport E - (f₂ (s a))) (H-s a) ⟩
          transport E (f₁-s a ∙ ap s (H a)) (f₂ (s a))
            ≡⟨ transport-∙ E (f₁-s a) (ap s (H a)) (f₂ (s a)) ⁻¹ ⟩
          transport E (ap s (H a)) (transport E (f₁-s a) (f₂ (s a)))
            ≡⟨ ap (λ - → transport E (ap s (H a)) (transport E - (f₂ (s a)))) (htpy-agreement a ⁻¹)  ⟩
          transport E (ap s (H a)) (transport E (f-s₁ a) (f₂ (s a)))
            ≡⟨ ap (transport E (ap s (H a))) (f-s₂ a) ⟩
          transport E (ap s (H a)) (s' (f₁ a) (f₂ a))
            ≡⟨ ℍ (f₁ a) (λ b p → transport E (ap s p) (s' (f₁ a) (f₂ a)) ≡ s' b (transport E p (f₂ a))) (refl _) a (H a) ⟩
          s' a (transport E (H a) (f₂ a)) ∎


-- Simpler proof of same theorem (use of π₁ is completely unnecessary)

ishinit-to-isind' : (A : Alg 𝓤) → ishinit 𝓤 A → isind 𝓤 A
ishinit-to-isind' {𝓤} (A , a₀ , s , i) init (E , e₀ , s' , j) = g , g₀ , g-s

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


-- ?. Preservation of Equivalences

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


-- ?. Equivalence Preservation is Function Preservation

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

  open Preservation-of-Equivalences

  ishae-pres-is-Contr : (A₁ A₂ : 𝓤 ̇) (e : A₁ ≃ A₂) (B₁ B₂ : 𝓥 ̇) (e' : B₁ ≃ B₂) (f₁ : A₁ → B₁) (f₂ : A₂ → B₂) (f-s : f₂ ∘ pr₁ e ∼ pr₁ e' ∘ f₁) → isContr (ishae-pres A₁  A₂ e B₁ B₂ e' f₁ f₂ f-s)
  ishae-pres-is-Contr {𝓤} {𝓥} = 𝕁-≃ (λ A₁ A₂ e → (B₁ B₂ : 𝓥 ̇) (e' : B₁ ≃ B₂) (f₁ : A₁ → B₁) (f₂ : A₂ → B₂) (f-s : f₂ ∘ pr₁ e ∼ pr₁ e' ∘ f₁) → isContr (ishae-pres A₁ A₂ e B₁ B₂ e' f₁ f₂ f-s)) λ A →
    𝕁-≃ (λ B₁ B₂ e' → (f₁ : A → B₁) (f₂ : A → B₂) (f-s : f₂ ∘ id ∼ pr₁ e' ∘ f₁) → isContr (ishae-pres A A (≃-refl A) B₁ B₂ e' f₁ f₂ f-s)) λ B f₁ f₂ →
      𝕁-∼ (λ f₂ f₁ f-s → isContr (ishae-pres A A (≃-refl A) B B (≃-refl B) f₁ f₂ f-s)) (λ f → ishae-pres-is-Contr' A B f) f₂ f₁

hae-pres-≃-fun-pres : (A₁ A₂ : 𝓤 ̇) (e : A₁ ≃ A₂) (B₁ B₂ : 𝓥 ̇) (e' : B₁ ≃ B₂) (f₁ : A₁ → B₁) (f₂ : A₂ → B₂) → hae-pres A₁ A₂ e B₁ B₂ e' f₁ f₂ ≃ (f₂ ∘ pr₁ e ∼ pr₁ e' ∘ f₁)
hae-pres-≃-fun-pres A₁ A₂ e B₁ B₂ e' f₁ f₂ = Σ-of-Contr-family-is-base _ _ (ishae-pres-is-Contr A₁ A₂ e B₁ B₂ e' f₁ f₂)

fun-pres-to-hae-pres : {A₁ A₂ : 𝓤 ̇} (e : A₁ ≃ A₂) {B₁ B₂ : 𝓥 ̇} (e' : B₁ ≃ B₂) (f₁ : A₁ → B₁) (f₂ : A₂ → B₂) → (f₂ ∘ pr₁ e ∼ pr₁ e' ∘ f₁) → hae-pres A₁ A₂ e B₁ B₂ e' f₁ f₂
fun-pres-to-hae-pres {𝓤} {𝓥} {A₁} {A₂} e {B₁} {B₂} e' f₁ f₂ = inv (hae-pres-≃-fun-pres A₁ A₂ e B₁ B₂ e' f₁ f₂)


-- ?. The Integers as Signed Natural Numbers

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


-- ?. ℤω is initial

ℤω-has-rec : hasrec 𝓤 ℤω-alg
ℤω-has-rec (A , a₀ , s , p , σ , ρ , τ) = f , refl _ , f-s where
  f : ℤω → A
  f 0ω = a₀
  f (strpos zero) = s a₀
  f (strpos (succ n)) = s (f (strpos n))
  f (strneg zero) = p a₀
  f (strneg (succ n)) = p (f (strneg n))
  f-s : f ∘ succω ∼ s ∘ f
  f-s 0ω = refl (s a₀)
  f-s (strpos n) = refl (s (f (strpos n)))
  f-s (strneg zero) = ρ a₀ ⁻¹
  f-s (strneg (succ n)) = ρ (f (strneg n)) ⁻¹ 

ℤω-has-rec-unique : hasrecunique 𝓤 ℤω-alg
ℤω-has-rec-unique {𝓤} (A , a₀ , s , p , σ , ρ , τ) (f , f₀ , f-s) (g , g₀ , g-s) with pr₂ (fun-pres-to-hae-pres ℤω-≃ (s , p , σ , ρ , τ) f f f-s) | pr₂ (fun-pres-to-hae-pres ℤω-≃ (s , p , σ , ρ , τ) g g g-s)
... | (f-p , f-σ , f-ρ , f-τ) | (g-p , g-σ , g-ρ , g-τ) = Hom-≡-intro ℤω-alg (A , a₀ , s , p , σ , ρ , τ) _ _ (H , H₀ , H-s)
  where
  H : f ∼ g
  H 0ω = f₀ ∙ g₀ ⁻¹
  H (strpos zero) = f-s 0ω ∙ ap s (H 0ω) ∙ g-s 0ω ⁻¹
  H (strpos (succ n)) = f-s (strpos n) ∙ ap s (H (strpos n)) ∙ g-s (strpos n) ⁻¹
  H (strneg zero) = f-p 0ω ∙ ap p (H 0ω) ∙ g-p 0ω ⁻¹
  H (strneg (succ n)) = f-p (strneg n) ∙ ap p (H (strneg n)) ∙ g-p (strneg n) ⁻¹
  H₀ : H 0ω ≡ f₀ ∙ g₀ ⁻¹
  H₀ = refl _
  aux1 : {a₁ a₂ a₃ a₄ x y : A} (p₁ : a₁ ≡ _) (p₂ : a₂ ≡ _) (p₃ : a₃ ≡ _) (p₄ : a₄ ≡ _) (q : x ≡ y) → (p₂ ∙ ap s p₁) ∙ ap (s ∘ p) q ∙ (p₄ ∙ ap s p₃) ⁻¹ ≡ p₂ ∙ ap s (p₁ ∙ ap p q ∙ p₃ ⁻¹) ∙ p₄ ⁻¹
  aux1 (refl _) (refl _) (refl _) (refl _) (refl _) = refl _
  H-s : (z : ℤω) → H (succω z) ≡ f-s z ∙ ap s (H z) ∙ g-s z ⁻¹
  H-s 0ω = refl (f-s 0ω ∙ ap s (H 0ω) ∙ g-s 0ω ⁻¹)
  H-s (strpos n) = refl (f-s (strpos n) ∙ ap s (H (strpos n)) ∙ g-s (strpos n) ⁻¹)
  H-s (strneg zero) = ap-id (H 0ω) ⁻¹ ∙ hnat' ρ (H 0ω) ⁻¹ ∙ (aux2 ✦ refl _ ✦ aux3) ∙ aux1 _ _ _ _ _ where
    aux2 : ρ (f 0ω) ⁻¹ ≡ f-s (strneg zero) ∙ ap s (f-p 0ω)
    aux2 = lu _ ∙ (f-ρ 0ω ∙ᵣ ρ (f 0ω) ⁻¹) ∙ ∙-assoc _ _ _ ⁻¹ ∙ (_ ∙ₗ rinv _) ∙ ru _ ⁻¹
    aux3 : ρ (g 0ω) ≡ (g-s (strneg zero) ∙ ap s (g-p 0ω)) ⁻¹
    aux3 = ⁻¹-invol _ ⁻¹ ∙ ap _⁻¹ (lu _ ∙ (g-ρ 0ω ∙ᵣ ρ (g 0ω) ⁻¹) ∙ ∙-assoc _ _ _ ⁻¹ ∙ (_ ∙ₗ rinv _) ∙ ru _ ⁻¹)
  H-s (strneg (succ n)) = ap-id (H (strneg n)) ⁻¹ ∙ hnat' ρ (H (strneg n)) ⁻¹ ∙ (aux2 ✦ refl _ ✦ aux3) ∙ aux1 _ _ _ _ _ where
    aux2 : ρ (f (strneg n)) ⁻¹ ≡ f-s (strneg (succ n)) ∙ ap s (f-p (strneg n))
    aux2 = lu _ ∙ (f-ρ (strneg n) ∙ᵣ ρ (f (strneg n)) ⁻¹) ∙ ∙-assoc _ _ _ ⁻¹ ∙ (_ ∙ₗ rinv _) ∙ ru _ ⁻¹
    aux3 : ρ (g (strneg n)) ≡ (g-s (strneg (succ n)) ∙ ap s (g-p (strneg n))) ⁻¹
    aux3 = ⁻¹-invol _ ⁻¹ ∙ ap _⁻¹ (lu _ ∙ (g-ρ (strneg n) ∙ᵣ ρ (g (strneg n)) ⁻¹) ∙ ∙-assoc _ _ _ ⁻¹ ∙ (_ ∙ₗ rinv _) ∙ ru _ ⁻¹)

ℤω-is-init : (𝓤 : Universe) → ishinit 𝓤 ℤω-alg
ℤω-is-init 𝓤 A = pr₂ isContr-iff-is-inhabited-Prop ((ℤω-has-rec A) , (ℤω-has-rec-unique A))


-- ?. Integers as HIT

postulate

  -- (i) Type formation
  
  ℤₕ : 𝓤₀ ̇

  -- (ii) Constructors
  
  0ₕ : ℤₕ
  succₕ : ℤₕ → ℤₕ
  predₕ : ℤₕ → ℤₕ
  secₕ : predₕ ∘ succₕ ∼ id
  retₕ : succₕ ∘ predₕ ∼ id
  cohₕ : (z : ℤₕ) → ap succₕ (secₕ z) ≡ retₕ (succₕ z)

ℤₕ-≃ : ℤₕ ≃ ℤₕ
ℤₕ-≃ = (succₕ , predₕ , secₕ , retₕ , cohₕ)

ℤₕ-alg : Alg 𝓤₀
ℤₕ-alg = (ℤₕ , 0ₕ , succₕ , predₕ , secₕ , retₕ , cohₕ)

postulate

  -- (iii) Eliminator

  ℤₕ-ind : (E : FibAlg 𝓥 ℤₕ-alg) → (z : ℤₕ) → (pr₁ E) z

  -- (iv) Computation rules

  0-β : (E : FibAlg 𝓥 ℤₕ-alg) → ℤₕ-ind E 0ₕ ↦ pr₁ (pr₂ E)  

  {-# REWRITE 0-β #-}

  succ-β : (E : FibAlg 𝓥 ℤₕ-alg) (z : ℤₕ) → ℤₕ-ind E (succₕ z) ↦ pr₁ (pr₂ (pr₂ E)) z (ℤₕ-ind E z)

  {-# REWRITE succ-β #-}


ℤₕ-is-ind : (𝓤 : Universe) → isind 𝓤 ℤₕ-alg
ℤₕ-is-ind 𝓤 (E , e₀ , s' , j) = let f = ℤₕ-ind (E , e₀ , s' , j) in
  f , (refl _) , (λ z → refl _)

ℤₕ-is-init : ishinit 𝓤₀ ℤₕ-alg
ℤₕ-is-init = isind-to-ishinit ℤₕ-alg (ℤₕ-is-ind 𝓤₀)

ℤₕ-is-ℤω : ℤₕ-alg ≡ ℤω-alg
ℤₕ-is-ℤω = ap pr₁ (InitAlg-is-Prop 𝓤₀ (ℤₕ-alg , ℤₕ-is-init) (ℤω-alg , ℤω-is-init 𝓤₀))


-- FIX UNIVALENCE: ISSUE IS WITH UNIVERSE

-- -- ?. Fibered Algebras and the Slice Categories
-- {-
-- χ : (B : Alg 𝓤) → (Σ A ꞉ Alg 𝓤 , Hom A B) → FibAlg 𝓤 B
-- χ (B , b₀ , s' , p' , σ' , ρ' , τ') ((A , a₀ , s , p , σ , ρ , τ) , (f , f₀ , f-s)) with pr₂ (fun-pres-to-hae-pres (s , p , σ , ρ , τ) (s' , p' , σ' , ρ' , τ') f f f-s)
-- ... | (f-p , f-ρ , f-σ , f-τ) = (fib f) , (a₀ , f₀) , ({!!} , {!!}) where
--   t : (b : B) → fib f b → fib f (s' b)
--   t b (a , q) = (s a) , (f-s a ∙ ap s' q)
--   tinv : (b : B) → fib f (s' b) → fib f b
--   tinv b (a , q) = p a , (f-p a ∙ ap p' q ∙ σ' b)
--   α : (b : B) → t b ∘ tinv b ∼ id
--   α b (a , q) = inv (path-space-fib _ _) (ρ a , {!!}) --doable
--   β : (b : B) → tinv b ∘ t b ∼ id
--   β b (a , q) = {!!} --doable

-- ψ : (B : Alg 𝓤) → FibAlg 𝓤 B → (Σ A ꞉ Alg 𝓤 , Hom A B)
-- ψ B E = (TotAlg B E) , (π₁ B E) 

-- χ∘ψ : (B : Alg 𝓤) → χ B ∘ ψ B ∼ id
-- χ∘ψ B E = {!!} -- identity of fibered algebras?

-- ψ∘χ : (B : Alg 𝓤) → ψ B ∘ χ B ∼ id
-- ψ∘χ B (A , f) = {!!} -- identity of (A , f) pairs? Have to transport f

-- equiv : (B : Alg 𝓤) → FibAlg 𝓤 B ≃ (Σ A ꞉ Alg 𝓤 , Hom A B)
-- equiv B = {!!} 
-- -}
-- -- Seems easier to work with equivalences and then contract...

-- module slice (𝓤 : Universe) where

--   Eqv⊙ : 𝓤 ⁺ ̇ 
--   Eqv⊙ = Σ A₁ ꞉ (𝓤 ̇) , Σ A₂ ꞉ (𝓤 ̇) , A₁ × (A₁ ≃ A₂)

--   -- Eqv⊙ is equivalent to the type of pointed maps

--   HomEqv⊙ : Eqv⊙ → Eqv⊙ → 𝓤 ̇
--   HomEqv⊙ (A₁ , A₂ , a₀ , s , i) (B₁ , B₂ , b₀ , s' , j) = Σ f₁ ꞉ (A₁ → B₁) , Σ f₂ ꞉ (A₂ → B₂) , (f₁ a₀ ≡ b₀) × (f₂ ∘ s ∼ s' ∘ f₁)

--   -- Once we contract the pointed equivalences to pointed types, we can contract the homotopies to pointed maps.

--   FibEqv⊙ : Eqv⊙ → 𝓤 ⁺ ̇
--   FibEqv⊙ (A₁ , A₂ , a₀ , s , i) = Σ E₁ ꞉ (A₁ → 𝓤 ̇) , Σ E₂ ꞉ (A₂ → 𝓤 ̇) , E₁ a₀ × (Σ s' ꞉ ((a₁ : A₁) → E₁ a₁ → E₂ (s a₁)) , ((a₁ : A₁) → isequiv (s' a₁)))

--   SecEqv⊙ : (A : Eqv⊙) → FibEqv⊙ A → 𝓤 ̇
--   SecEqv⊙ (A₁ , A₂ , a₀ , s , i) (E₁ , E₂ , e₀ , s' , j) = Σ f₁ ꞉ Π E₁ , Σ f₂ ꞉ Π E₂ , (f₁ a₀ ≡ e₀) × ((a₁ : A₁) → f₂ (s a₁) ≡ s' a₁ (f₁ a₁))

--   lemma1 : (A : 𝓤 ̇) (a₀ : A) → FibEqv⊙ (A , A , a₀ , ≃-refl A) ≃ (Σ E ꞉ (A → 𝓤 ̇) , E a₀)
--   lemma1 A a₀ = {!!}

--   lemma₂ : (B : 𝓤 ̇) (b₀ : B) → (Σ A ꞉ Eqv⊙ , HomEqv⊙ A (B , B , b₀ , ≃-refl B)) ≃ {!!}
--   lemma₂ = {!!}

--   claim : (B : Eqv⊙) → (Σ A ꞉ Eqv⊙ , HomEqv⊙ A B) ≃ FibEqv⊙ B
--   claim (B₁ , B₂ , b₀ , t) = ℍ-≃ B₁ (λ B₂ t → (b₀ : B₁) → (Σ A ꞉ Eqv⊙ , HomEqv⊙ A (B₁ , B₂ , b₀ , t)) ≃ FibEqv⊙ (B₁ , B₂ , b₀ , t)) (λ b₀ → {!!} ● ≃-sym (lemma1 B₁ b₀)) B₂ t b₀

--   -- The claim ultimately reduces to the case of pointed types.


-- {- Extra stuff
-- ishae↓ : {A : 𝓤 ̇} {B : 𝓥 ̇} {P : A → 𝓦 ̇} (Q : B → 𝓣 ̇) (f : A → B) → ((a : A) → P a → Q (f a)) → 𝓤 ⊔ 𝓦 ⊔ 𝓣 ̇
-- ishae↓ {𝓤} {𝓥} {𝓦} {𝓣} {A} {B} {P} Q f g =
--   Σ ginv ꞉ ((a : A) → Q (f a) → P a) ,
--   Σ η ꞉ ((a : A) → (ginv a) ∘ (g a) ∼ id) ,
--   Σ ε ꞉ ((a : A) → (g a) ∘ (ginv a) ∼ id) ,
--   ((a : A) (u : P a) → ap (g a) (η a u) ≡ (ε a) (g a u) )

-- ishae↓-to-fiberwise-≃ : {A : 𝓤 ̇} {B : 𝓥 ̇} {P : A → 𝓦 ̇} (Q : B → 𝓣 ̇) (f : A → B) (g : (a : A) → P a → Q (f a)) → ishae↓ Q f g → ((a : A) → ishae (g a)) 
-- ishae↓-to-fiberwise-≃ Q f g (ginv , η , ε , τ) a = ginv a , η a , ε a , τ a

-- fiberwise-≃-to-ishae↓ : {A : 𝓤 ̇} {B : 𝓥 ̇} {P : A → 𝓦 ̇} (Q : B → 𝓣 ̇) (f : A → B) (g : (a : A) → P a → Q (f a)) → ((a : A) → ishae (g a)) → ishae↓ Q f g
-- fiberwise-≃-to-ishae↓ {𝓤} {𝓥} {𝓦} {𝓣} {A} {B} {P} Q f g i = {!!} where
--   ginv : ((a : A) → Q (f a) → P a)
--   ginv a = ishae₁ (i a)
--   η : ((a : A) → (ginv a) ∘ (g a) ∼ id)
--   η a = ishae₂ (i a)
--   ε : ((a : A) → (g a) ∘ (ginv a) ∼ id)
--   ε a = ishae₃ (i a)
--   τ : (a : A) (u : P a) → ap (g a) (η a u) ≡ (ε a) (g a u)
--   τ a = ishae₄ (i a)
-- -}

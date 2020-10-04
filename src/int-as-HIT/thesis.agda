{-# OPTIONS --without-K --exact-split --safe #-}

open import Ch1.Type-theory
open import Ch2.Homotopy-type-theory
open import Ch3.Sets-and-logic
open import Ch4.Equivalences
open import Ch5.8-Id-types-and-id-systems

module int-as-HIT.thesis ⦃ fe : FunExt ⦄ where


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
  comp A B C (g , g₀ , g-β) (f , f₀ , f-β) = g ∘ f , (ap g f₀ ∙ g₀) , λ a → ap g (f-β a) ∙ g-β (f a)

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
  HomId (f , f₀ , f-β) (g , g₀ , g-β) = Σ H ꞉ (f ∼ g) , (H a₀ ⁻¹ ∙ f₀ ≡ g₀) × ((a : A) → f-β a ∙ ap t (H a) ≡ H (s a) ∙ g-β a)

  -- From path to extension

  Hom-≡-elim : (f' g' : Hom A' B') → f' ≡ g' → HomId f' g'
  Hom-≡-elim f' .f' (refl .f') = hrefl _ , (lu _ ⁻¹) , λ a → ru _ ⁻¹ ∙ lu _

  -- The total space of HomId f' is contractible

  module TotHomId-is-Contr (f : A → B) (f₀ : f a₀ ≡ b₀) (f-β : f ∘ s ∼ t ∘ f) where

    f' : Hom A' B'
    f' = (f , f₀ , f-β)

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
    Tot-htpy (g , H) = Σ g-β ꞉ (g ∘ s ∼ t ∘ g) , ((a : A) → f-β a ∙ ap t (H a) ≡ H (s a) ∙ g-β a)

    Tot-htpy-is-Contr : isContr (Tot-htpy (f , hrefl f))
    Tot-htpy-is-Contr = ≃-preserves-Contr ((split , dep-Σ-UMP A (λ a → f (s a) ≡ t (f a)) λ a x → f-β a ∙ refl (t (f a)) ≡ refl (f (s a)) ∙ x)) (Π-preserves-Contr _ λ a → ≃-preserves-Contr (Σ-preserves-family-≃ (λ x → post-∙-≃ (f-β a ∙ refl _) (lu _))) (free-right-endpt-is-Contr _ _))

    TotHomId' : 𝓤 ⊔ 𝓥 ̇
    TotHomId' = Σ w ꞉ Tot-fun , Tot-path w × Tot-htpy w

    TotHomId'-is-Contr : isContr (TotHomId')
    TotHomId'-is-Contr = ≃-preserves-Contr (≃-sym (Σ-over-Contr-base-is-fib _ _ Tot-fun-is-Contr)) (×-preserves-Contr _ _ Tot-path-is-Contr Tot-htpy-is-Contr)

    -- Correctness of decomposition

    ϕ : TotHomId → TotHomId'
    ϕ ((g , g₀ , g-β) , (H , H₀ , H-β)) = (g , H) , (g₀ , H₀) , (g-β , H-β)

    ψ : TotHomId' → TotHomId
    ψ ((g , H) , (g₀ , H₀) , (g-β , H-β)) = ((g , g₀ , g-β) , (H , H₀ , H-β))

    TotHomId-is-Contr : isContr (TotHomId)
    TotHomId-is-Contr = ≃-preserves-Contr (≃-sym (ϕ , qinv-to-isequiv (ψ , hrefl _ , hrefl _))) TotHomId'-is-Contr

  open TotHomId-is-Contr using (TotHomId-is-Contr) public

  -- Equivalence (Fundamental Theorem of Id Types)

  IdHom-≃-HomId : (f' g' : Hom A' B') → (f' ≡ g') ≃ HomId f' g' 
  IdHom-≃-HomId (f , f₀ , f-β) g' = Hom-≡-elim (f , f₀ , f-β) g' , pr₂ (fiberwise-≃-iff-total-≃.Hae (Hom-≡-elim (f , f₀ , f-β))) (map-between-Contrs-is-equiv _ (free-right-endpt-is-Contr _ _) (TotHomId-is-Contr f f₀ f-β)) g'

  -- From extension to path

  Hom-≡-intro : (f' g' : Hom A' B') → HomId f' g' → f' ≡ g'
  Hom-≡-intro f' g' = inv (IdHom-≃-HomId f' g')  

open Morphism-Id using (HomId ; Hom-≡-elim ; Hom-≡-intro) public 


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
  sec-to-hom (A , a₀ , s , i) (E , e₀ , s' , j) (f , f₀ , f-β) = (λ a → a , f a) , dpair-≡ (refl a₀ , f₀) , λ a → dpair-≡ (refl (s a) , f-β a)

  -- Sections are sections

  sec-to-hom-gives-section : (A : Alg 𝓤) (E : FibAlg 𝓥 A) (f : AlgSec A E) → comp A (TotAlg A E) A (π₁ A E) (sec-to-hom A E f) ≡ algid A
  sec-to-hom-gives-section (A , a₀ , s , i) (E , e₀ , s' , j) (f , f₀ , f-β) =
    Hom-≡-intro (A , a₀ , s , i) (A , a₀ , s , i) _ _ (
      hrefl _ ,
      (lu _ ⁻¹ ∙ (ru _ ⁻¹ ∙ dpr₁-≡-β (refl a₀) f₀)) ,
      λ a → ru _ ⁻¹ ∙ ru _ ⁻¹ ∙ dpr₁-≡-β (refl (s a)) (f-β a)
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
    
  -- Characterize identity type of sections (isind is a proposition)

open Fibered-Algebras public


module Inductive-Algebras where

  isind : (𝓥 : Universe) → Alg 𝓤 → 𝓤 ⊔ 𝓥 ⁺ ̇
  isind 𝓥 A = (E : FibAlg 𝓥 A) → AlgSec A E

  {- Postpone:

  module Uniquenes-Pple-for-Ind (𝓥 : Universe) (A : Alg 𝓤) (indA : isind 𝓥 A) where

    -- need identity type of sections

  isind-is-Prop : (𝓥 : Universe) (A : Alg 𝓤) → isProp (isind 𝓥 A)
  isind-is-Prop = {!!} -- need uniqueness pple  

  -}

open Inductive-Algebras public


module Homotopy-Initial-Algebras where

  ishinit : (𝓥 : Universe) → Alg 𝓤 → 𝓤 ⊔ 𝓥 ⁺ ̇
  ishinit 𝓥 A = (B : Alg 𝓥) → isContr (Hom A B)

  ishinit-is-Prop : (𝓥 : Universe) (A : Alg 𝓤) → isProp (ishinit 𝓥 A)
  ishinit-is-Prop 𝓥 A = Π-preserves-Props _ (λ B → isContr-is-Prop _)

  hasrec : (𝓥 : Universe) → Alg 𝓤 → 𝓤 ⊔ 𝓥 ⁺ ̇
  hasrec 𝓥 A = (B : Alg 𝓥) → Hom A B

  hasrecunique : (𝓥 : Universe) (A : Alg 𝓤) → 𝓤 ⊔ 𝓥 ⁺ ̇
  hasrecunique 𝓥 A = (B : Alg 𝓥) → isProp (Hom A B)

open Homotopy-Initial-Algebras public


module Inductive-to-Initial where

  -- Prove that initiality implies induction principle without coherence condition (i.e. just quasi-inverses). Then prove initiality only for the HIT with that induction principle. Problem: that HIT is not a set, so it shouldn't be possible to prove this.

  isind-to-hasrec : (A : Alg 𝓤) → isind 𝓤 A → hasrec 𝓤 A
  isind-to-hasrec A A-ind B = A-ind (Alg-to-FibAlg A B)

  isind-to-hasrecunique : (A : Alg 𝓤) → isind 𝓤 A → hasrecunique 𝓤 A
  isind-to-hasrecunique {𝓤} (A , a₀ , s , p , σ , ρ , τ)  A-ind (B , b₀ , s' , p' , σ' , ρ' , τ') (f , f₀ , f-β) (g , g₀ , g-β) = Hom-≡-intro A' B' _ _ ({!!} , {!!} , {!!}) where
    A' : Alg 𝓤
    A' = (A , a₀ , s , p , σ , ρ , τ)
    B' : Alg 𝓤
    B' = (B , b₀ , s' , p' , σ' , ρ' , τ')
    ϕ : (Σ a ꞉ A , f a ≡ g a) → (Σ a ꞉ A , f a ≡ g a)
    ϕ (a , ih) = (s a) , (f-β a ∙ ap s' ih ∙ g-β a ⁻¹)
    ψ : (Σ a ꞉ A , f a ≡ g a) → (Σ a ꞉ A , f a ≡ g a)
    ψ (a , ih) = p a , {!!} -- Here we need computation rules! And we will need sth similar for the section in order to prove isind is a proposition. But we do not need to recorver the computation rules for the coherence condition, so it might not be so complicated after all.
    α : ϕ ∘ ψ ∼ id
    α (a , ih) = {!!}
    β : ψ ∘ ϕ ∼ id
    β (a , ih) = {!!}
    E : FibAlg 𝓤 A'
    E = (λ a → f a ≡ g a) , (f₀ ∙ g₀ ⁻¹) , (λ a ih → f-β a ∙ ap s' ih ∙ g-β a ⁻¹) , qinv-to-isequiv (ψ , α , β)

  isind-to-ishinit : (A : Alg 𝓤) → isind 𝓤 A → ishinit 𝓤 A
  isind-to-ishinit (A , a₀ , s , i) A-ind = {!!}


module Initial-to-Inductive where

  ishinit-to-isind : (A : Alg 𝓤) → ishinit 𝓤 A → isind 𝓤 A
  ishinit-to-isind {𝓤} (A , a₀ , s , i) init (E , e₀ , s' , j) = g , g₀ , g-β
 
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

    f-β : f ∘ s ∼ total↓ E s s' ∘ f
    f-β = pr₂ (pr₂ A-rec)

    -- 2.1 First components of f

    f₁ : A → A
    f₁ = pr₁ ∘ f

    f₀₁ : f₁ a₀ ≡ a₀
    f₀₁ = pr₁ (dpr-≡ f₀)

    f-β₁ : f₁ ∘ s ∼ s ∘ f₁
    f-β₁ a = pr₁ (dpr-≡ (f-β a))

    -- 2.2 Second components of f

    f₂ : (a : A) → E (f₁ a)
    f₂ = pr₂ ∘ f

    f₀₂ : transport E f₀₁ (f₂ a₀) ≡ e₀
    f₀₂ = pr₂ (dpr-≡ f₀)

    f-β₂ : (a : A) → transport E (f-β₁ a) (f₂ (s a)) ≡ s' (f₁ a) (f₂ a)
    f-β₂ a = pr₂ (dpr-≡ (f-β a))

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
    f₁-β a = ap pr₁ (f-β a) ∙ refl _
    _ : f₁-β ≡ pr₂ (pr₂ π₁∘f)
    _ = refl _

    -- 3.1 First components of f agree with composite π₁∘f

    path-agreement : f₀₁ ≡ f₁₀
    path-agreement = ap pr₁ (dpr-≡-agreement f₀) ∙ ru _

    htpy-agreement : f-β₁ ∼ f₁-β
    htpy-agreement a = ap pr₁ (dpr-≡-agreement (f-β a)) ∙ ru _

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
           
    g-β : (a : A) → g (s a) ≡ s' a (g a)
    g-β a = transport E (H (s a)) (f₂ (s a))
              ≡⟨ ap (λ - → transport E - (f₂ (s a))) (H-β' a) ⟩
            transport E (f₁-β a ∙ ap s (H a)) (f₂ (s a))
              ≡⟨ transport-∙ E (f₁-β a) (ap s (H a)) (f₂ (s a)) ⁻¹ ⟩
            transport E (ap s (H a)) (transport E (f₁-β a) (f₂ (s a)))
              ≡⟨ ap (λ - → transport E (ap s (H a)) (transport E - (f₂ (s a)))) (htpy-agreement a ⁻¹)  ⟩
            transport E (ap s (H a)) (transport E (f-β₁ a) (f₂ (s a)))
              ≡⟨ ap (transport E (ap s (H a))) (f-β₂ a) ⟩
            transport E (ap s (H a)) (s' (f₁ a) (f₂ a))
              ≡⟨ ℍ (f₁ a) (λ b p → transport E (ap s p) (s' (f₁ a) (f₂ a)) ≡ s' b (transport E p (f₂ a))) (refl _) a (H a) ⟩
            s' a (transport E (H a) (f₂ a)) ∎


  -- Show initiality implies induction principle for some notion of fibered algebra and algebra section. The latter notion is clear; the former should just provide data to get an equivalence. So maybe we can use the notion of inductive below to get the proof going and then provide a definition of fibered algebra. The key point is that the definition of algebra section is independent of the definition of fibered algebra (at least with respect to the higher paths). 


  
  

-- -- I. ℕ- and ℤ-Algebras

-- ℕAlg : (𝓤 : Universe) → 𝓤 ⁺ ̇
-- ℕAlg 𝓤 = Σ A ꞉ (𝓤 ̇) , A × (A → A)

-- ℤAlg : (𝓤 : Universe) → 𝓤 ⁺ ̇
-- ℤAlg 𝓤 = Σ A ꞉ (𝓤 ̇) , A × (Σ s ꞉ (A → A) , ishae s)

-- {- Notation:

-- ℤAlg 𝓤 = Σ A ꞉ (𝓤 ̇) ,
--          Σ a₀ ꞉ A ,
--          Σ s ꞉ (A → A) ,
--          Σ p ꞉ (A → A) ,
--          Σ σ ꞉ (p ∘ s ∼ id) ,
--          Σ ρ ꞉ (s ∘ p ∼ id) ,
--          ((a : A) → ap s (σ a) ≡ ρ (s a)) -- τ

-- -}


-- -- II. ℕ- and ℤ-Algebra Homomorphisms

-- -- Equivalences as objects

-- Eqv : (𝓤 : Universe) → 𝓤 ⁺ ̇
-- Eqv 𝓤 = Σ A₁ ꞉ (𝓤 ̇) , Σ A₂ ꞉ (𝓤 ̇) , A₁ ≃ A₂

-- -- Equivalence-preserving maps

-- module EqvPreservation {A₁ A₂ : 𝓤 ̇} {B₁ B₂ : 𝓥 ̇} (f₁ : A₁ → B₁) (f₂ : A₂ → B₂) where

--   module MapPreservation where

--     s-pres : (A₁ → A₂) → (B₁ → B₂) → 𝓤 ⊔ 𝓥 ̇
--     s-pres s s' = f₂ ∘ s ∼ s' ∘ f₁

--     p-pres : (A₂ → A₁) → (B₂ → B₁) → 𝓤 ⊔ 𝓥 ̇
--     p-pres p p' = f₁ ∘ p ∼ p' ∘ f₂

--   open MapPreservation public

--   module HtpyPreservation (s : A₁ → A₂) (p : A₂ → A₁) (s' : B₁ → B₂) (p' : B₂ → B₁) (α : s-pres s s') (β : p-pres p p') where

--     aux-γ : f₁ ∘ p ∘ s ∼ p' ∘ s' ∘ f₁
--     aux-γ a₁ = β (s a₁) ∙ ap p' (α a₁)

--     σ-pres : (p ∘ s ∼ id) → (p' ∘ s' ∼ id) → 𝓤 ⊔ 𝓥 ̇
--     σ-pres σ σ' = (a₁ : A₁) → ap f₁ (σ a₁) ≡ aux-γ a₁ ∙ σ' (f₁ a₁)

--     aux-δ : f₂ ∘ s ∘ p ∼ s' ∘ p' ∘ f₂
--     aux-δ a₂ = α (p a₂) ∙ ap s' (β a₂)

--     ρ-pres : (s ∘ p ∼ id) → (s' ∘ p' ∼ id) → 𝓤 ⊔ 𝓥 ̇
--     ρ-pres ρ ρ' = (a₂ : A₂) → ap f₂ (ρ a₂) ≡ aux-δ a₂ ∙ ρ' (f₂ a₂)

--   module CohPreservation (s : A₁ → A₂) (p : A₂ → A₁) (s' : B₁ → B₂) (p' : B₂ → B₁) (α : s-pres s s') (β : p-pres p p') where

--     open HtpyPreservation s p s' p' α β

--     aux-ε-γ₁ : f₂ ∘ s ∘ p ∘ s ∼ s' ∘ p' ∘ s' ∘ f₁
--     aux-ε-γ₁ a₁ = α (p (s a₁)) ∙ ap s' (aux-γ a₁)

--     aux-ε-δ₁ : f₂ ∘ s ∘ p ∘ s ∼ s' ∘ p' ∘ s' ∘ f₁
--     aux-ε-δ₁ a₁ = aux-δ (s a₁) ∙ ap s' (ap p' (α a₁))

--     aux-ε-γ₁-is-aux-ε-δ₁ : aux-ε-γ₁ ∼ aux-ε-δ₁
--     aux-ε-γ₁-is-aux-ε-δ₁ a₁ = (refl (α (p (s a₁))) ✦ ap-∙ s' _ _) ∙ ∙-assoc _ _ _

--     aux-ε-γ₂ : (σ : p ∘ s ∼ id) (σ' : p' ∘ s' ∼ id) → ((a₁ : A₁) → ap f₁ (σ a₁) ≡ aux-γ a₁ ∙ σ' (f₁ a₁)) → (a₁ : A₁) → ap f₂ (ap s (σ a₁)) ∙ α a₁ ≡ aux-ε-γ₁ a₁ ∙ ap s' (σ' (f₁ a₁))
--     aux-ε-γ₂ σ σ' γ a₁ = (ap-∘ s f₂ (σ a₁) ✦ refl (α a₁)) ∙ hnat α (σ a₁) ⁻¹ ∙ (refl (α (p (s a₁))) ✦ (ap-∘ f₁ s' (σ a₁) ⁻¹ ∙ ap (ap s') (γ a₁) ∙ ap-∙ s' _ _)) ∙ ∙-assoc _ _ _

--     aux-ε-δ₂ : (ρ : s ∘ p ∼ id) (ρ' : s' ∘ p' ∼ id) → ((a₂ : A₂) → ap f₂ (ρ a₂) ≡ aux-δ a₂ ∙ ρ' (f₂ a₂)) → (a₁ : A₁) → ap f₂ (ρ (s a₁)) ∙ α a₁ ≡ aux-ε-δ₁ a₁ ∙ ρ' (s' (f₁ a₁))
--     aux-ε-δ₂ ρ ρ' δ a₁ = (δ (s a₁) ✦ ap-id (α a₁) ⁻¹) ∙ ∙-assoc _ _ _ ⁻¹ ∙ (refl (aux-δ (s a₁)) ✦ (hnat ρ' (α a₁) ∙ (ap-∘ p' s' (α a₁) ⁻¹ ✦ refl (ρ' (s' (f₁ a₁)))))) ∙ ∙-assoc _ _ _

--     τ-pres : (σ : p ∘ s ∼ id) (ρ : s ∘ p ∼ id) (τ : (a₁ : A₁) → ap s (σ a₁) ≡ ρ (s a₁)) (σ' : p' ∘ s' ∼ id) (ρ' : s' ∘ p' ∼ id) (τ' : (b₁ : B₁) → ap s' (σ' b₁) ≡ ρ' (s' b₁)) (γ : σ-pres σ σ') (δ : ρ-pres ρ ρ') → 𝓤 ⊔ 𝓥 ̇
--     τ-pres σ ρ τ σ' ρ' τ' γ δ = (a₁ : A₁) → (ap (ap f₂) (τ a₁) ✦ refl (α a₁)) ∙ aux-ε-δ₂ ρ ρ' δ a₁ ≡ aux-ε-γ₂ σ σ' γ a₁ ∙ (aux-ε-γ₁-is-aux-ε-δ₁ a₁ ✦ τ' (f₁ a₁))

-- hae-pres : (A : Eqv 𝓤) (B : Eqv 𝓥) → (pr₁ A → pr₁ B) → (pr₁ (pr₂ A) → pr₁ (pr₂ B)) → 𝓤 ⊔ 𝓥 ̇
-- hae-pres (A₁ , A₂ , s , p , σ , ρ , τ) (B₁ , B₂ , s' , p' , σ' , ρ' , τ') f₁ f₂ =
--   Σ α ꞉ s-pres s s' ,
--   Σ β ꞉ p-pres p p' ,
--   Σ γ ꞉ σ-pres α β σ σ' ,
--   Σ δ ꞉ ρ-pres α β ρ ρ' ,
--   τ-pres α β σ ρ τ σ' ρ' τ' γ δ
--   where open EqvPreservation f₁ f₂
--         open HtpyPreservation s p s' p'
--         open CohPreservation s p s' p'

-- hae-semipres : (A : Eqv 𝓤) (B : Eqv 𝓥) (f₁ : pr₁ A → pr₁ B) (f₂ : pr₁ (pr₂ A) → pr₁ (pr₂ B)) → EqvPreservation.s-pres f₁ f₂ (pr₁ (pr₂ (pr₂ A))) (pr₁ (pr₂ (pr₂ B))) → 𝓤 ⊔ 𝓥 ̇
-- hae-semipres (A₁ , A₂ , s , p , σ , ρ , τ) (B₁ , B₂ , s' , p' , σ' , ρ' , τ') f₁ f₂ α =
--   Σ β ꞉ p-pres p p' ,
--   Σ γ ꞉ σ-pres β σ σ' ,
--   Σ δ ꞉ ρ-pres β ρ ρ' ,
--   τ-pres β σ ρ τ σ' ρ' τ' γ δ
--   where open EqvPreservation f₁ f₂
--         open HtpyPreservation s p s' p' α
--         open CohPreservation s p s' p' α

-- EqvHom : Eqv 𝓤 → Eqv 𝓥 → 𝓤 ⊔ 𝓥 ̇
-- EqvHom A B = Σ f₁ ꞉ (pr₁ A → pr₁ B) , Σ f₂ ꞉ (pr₁ (pr₂ A) → pr₁ (pr₂ B)) , hae-pres A B f₁ f₂

-- -- Simple equivalence-preserving maps

-- module SimpleHom ⦃ fe : FunExt ⦄ (A : 𝓤 ̇) (B : 𝓥 ̇) (f : A → B) where

--   open EqvPreservation f f
--   open HtpyPreservation id id id id
--   open CohPreservation id id id id

--   abstract
  
--     lemma-1 : isContr (Σ β ꞉ p-pres id id , σ-pres (hrefl _) β (hrefl _) (hrefl _))
--     lemma-1 = ≃-preserves-Contr
--       (split , (dep-Σ-UMP A (λ a → f a ≡ f a) λ a βa → refl (f a) ≡ (βa ∙ refl (f a)) ∙ refl (f a)))
--       (Π-preserves-Contr _ (λ a → ≃-preserves-Contr (Σ-preserves-family-≃ (λ βa → post-∙-≃ (refl (f a)) (ru βa ∙ ru _))) (free-right-endpt-is-Contr _ _)))

--     lemma-2 : isContr (Σ δ ꞉ ρ-pres (hrefl _) (hrefl _) (hrefl _) (hrefl _) , τ-pres (hrefl _) (hrefl _) (hrefl _) (hrefl _) (hrefl _) (hrefl _) (hrefl _) (hrefl _) (hrefl _) δ)
--     lemma-2 = ≃-preserves-Contr
--       (split , (dep-Σ-UMP A (λ a → refl (f a) ≡ refl _ ∙ refl _ ∙ refl _) λ a δa → refl _ ∙ (refl _ ∙ δa ∙ refl _ ∙ refl _ ∙ refl _ ∙ refl _ ∙ refl _) ≡ refl (refl (f a))))
--       (Π-preserves-Contr _ (λ a → ≃-preserves-Contr (Σ-preserves-family-≃ (λ δa → pre-∙-≃ (refl (refl (f a))) (lu _ ⁻¹ ∙ ru _ ⁻¹ ∙ ru _ ⁻¹ ∙ ru _ ⁻¹ ∙ ru _ ⁻¹ ∙ ru _ ⁻¹ ∙ lu δa ⁻¹))) (free-left-endpt-is-Contr _ _)))

--     Contr-lemma : isContr (hae-semipres (A , A , ≃-refl A) (B , B , ≃-refl B) f f (hrefl _))
--     Contr-lemma = ≃-preserves-Contr (≃-sym (Σ-assoc _ _ _ ● Σ-over-Contr-base-is-fib _ _ lemma-1)) lemma-2

-- -- The corresponding forgetful functor is fully-faithful.

-- simple-homs : ⦃ fe : FunExt ⦄ ⦃ univ : Univalence ⦄ (A₁ A₂ : 𝓤 ̇) (e : A₁ ≃ A₂) (B₁ B₂ : 𝓥 ̇) (e' : B₁ ≃ B₂) (f₁ : A₁ → B₁) (f₂ : A₂ → B₂) → hae-pres (A₁ , A₂ , e) (B₁ , B₂ , e') f₁ f₂ ≃ (f₂ ∘ pr₁ e ∼ pr₁ e' ∘ f₁)
-- simple-homs {𝓤} {𝓥} = 𝕁-≃ (λ A₁ A₂ e → (B₁ B₂ : 𝓥 ̇) (e' : B₁ ≃ B₂) (f₁ : A₁ → B₁) (f₂ : A₂ → B₂) → hae-pres (A₁ , A₂ , e) (B₁ , B₂ , e') f₁ f₂ ≃ (f₂ ∘ pr₁ e ∼ pr₁ e' ∘ f₁)) λ A →
--   𝕁-≃ (λ B₁ B₂ e' → (f₁ : A → B₁) (f₂ : A → B₂) → hae-pres (A , A , ≃-refl A) (B₁ , B₂ , e') f₁ f₂ ≃ (f₂ ∘ id ∼ pr₁ e' ∘ f₁))
--   λ B f₁ f₂ →
--     Σ-of-Contr-family-is-base _ _ (𝕁-∼ (λ f₂ f₁ α → isContr (hae-semipres (A , A , ≃-refl A) (B , B , ≃-refl B) f₁ f₂ α)) (SimpleHom.Contr-lemma A B) f₂ f₁)

-- -- ℕ- and ℤ-Algebra homomorphisms

-- ℕHom : ℕAlg 𝓤 → ℕAlg 𝓥 → 𝓤 ⊔ 𝓥 ̇
-- ℕHom (A , a₀ , s) (B , b₀ , s') = Σ f ꞉ (A → B) , (f a₀ ≡ b₀) × (f ∘ s ∼ s' ∘ f)

-- ℤHom : ℤAlg 𝓤 → ℤAlg 𝓥 → 𝓤 ⊔ 𝓥 ̇
-- ℤHom (A , a₀ , s , s-is-hae) (B , b₀ , s' , s'-is-hae) = Σ f ꞉ (A → B) , (f a₀ ≡ b₀) × hae-pres (A , A , s , s-is-hae) (B , B , s' , s'-is-hae) f f

-- ℕcomp : (A : ℕAlg 𝓤) (B : ℕAlg 𝓥) (C : ℕAlg 𝓦) → ℕHom B C → ℕHom A B → ℕHom A C
-- ℕcomp (A , a₀ , s) (B , b₀ , t)  (C , c₀ , u) (g , q' , α') (f , q , α) = g ∘ f , (ap g q ∙ q') , λ a → ap g (α a) ∙ α' (f a) 

-- ℕid : (A : ℕAlg 𝓤) → ℕHom A A
-- ℕid A = id , refl _ , hrefl _
 
-- -- Identity type of ℕ-Algebra homomorphisms

-- ℕHomId : (A : ℕAlg 𝓤) (B : ℕAlg 𝓥) → ℕHom A B → ℕHom A B → 𝓤 ⊔ 𝓥 ̇
-- ℕHomId (A , a₀ , s) (B , b₀ , t) (f , q , α) (g , q' , α') = Σ H ꞉ (f ∼ g) , (q ≡ H a₀ ∙ q') × ((a : A) → α a ∙ ap t (H a) ≡ H (s a) ∙ α' a)

-- ℕHom-≡-elim : (A : ℕAlg 𝓤) (B : ℕAlg 𝓥) (f g : ℕHom A B) → f ≡ g → ℕHomId A B f g
-- ℕHom-≡-elim A B f .f (refl .f) = hrefl _ , lu _ , λ a → ru _ ⁻¹ ∙ lu _ 

-- ΣℕHomId-is-Contr : ⦃ fe : FunExt ⦄ (A : ℕAlg 𝓤) (B : ℕAlg 𝓥) (f : ℕHom A B) → isContr (Σ g ꞉ ℕHom A B , ℕHomId A B f g)
-- ΣℕHomId-is-Contr (A , a₀ , s) (B , b₀ , t) (f , q , α) = ≃-preserves-Contr (≃-sym (Σ-over-Contr-base-is-fib _ _ (≃-preserves-Contr (Σ-preserves-family-≃ (λ g → happly , happly-is-equiv)) (free-right-endpt-is-Contr _ _ ))) ● aux-equiv) (×-preserves-Contr _ _ {!!} {!!}) where
--   aux-to : (Σ w ꞉ (Σ g ꞉ (A → B) , (f ∼ g)) , (Σ q' ꞉ (pr₁ w a₀ ≡ b₀) , (q ≡ pr₂ w a₀ ∙ q')) × (Σ α' ꞉ (pr₁ w ∘ s ∼ t ∘ pr₁ w) , ((a : A) → α a ∙ ap t (pr₂ w a) ≡ pr₂ w (s a) ∙ α' a))) → (Σ g ꞉ ℕHom (A , a₀ , s) (B , b₀ , t) , ℕHomId (A , a₀ , s) (B , b₀ , t) (f , q , α) g)
--   aux-to ((g , H) , (q' , r) , (α' , ξ)) = ((g , q' , α') , (H , r , ξ))
--   aux-from : (Σ g ꞉ ℕHom (A , a₀ , s) (B , b₀ , t) , ℕHomId (A , a₀ , s) (B , b₀ , t) (f , q , α) g) → (Σ w ꞉ (Σ g ꞉ (A → B) , (f ∼ g)) , (Σ q' ꞉ (pr₁ w a₀ ≡ b₀) , (q ≡ pr₂ w a₀ ∙ q')) × (Σ α' ꞉ (pr₁ w ∘ s ∼ t ∘ pr₁ w) , ((a : A) → α a ∙ ap t (pr₂ w a) ≡ pr₂ w (s a) ∙ α' a)))
--   aux-from ((g , q' , α') , (H , r , ξ)) = ((g , H) , (q' , r) , (α' , ξ))
--   aux-to∘from : aux-to ∘ aux-from ∼ id
--   aux-to∘from ((g , q' , α') , (H , r , ξ)) = refl _
--   aux-from∘to : aux-from ∘ aux-to ∼ id
--   aux-from∘to ((g , H) , (q' , r) , (α' , ξ)) = refl _
--   aux-equiv : (Σ w ꞉ (Σ g ꞉ (A → B) , (f ∼ g)) , (Σ q' ꞉ (pr₁ w a₀ ≡ b₀) , (q ≡ pr₂ w a₀ ∙ q')) × (Σ α' ꞉ (pr₁ w ∘ s ∼ t ∘ pr₁ w) , ((a : A) → α a ∙ ap t (pr₂ w a) ≡ pr₂ w (s a) ∙ α' a))) ≃ (Σ g ꞉ ℕHom (A , a₀ , s) (B , b₀ , t) , ℕHomId (A , a₀ , s) (B , b₀ , t) (f , q , α) g)
--   aux-equiv = aux-to , qinv-to-isequiv (aux-from , aux-to∘from , aux-from∘to)


-- -- III. Forgetful Functor

-- U₀ : ℤAlg 𝓤 → ℕAlg 𝓤
-- U₀ (A , a₀ , s , s-is-hae) = (A , a₀ , s)

-- U₁ : (A : ℤAlg 𝓤) (B : ℤAlg 𝓥) → ℤHom A B → ℕHom (U₀ A) (U₀ B)
-- U₁ A B (f , q , α , etc) = f , q , α

-- -- U is injective on objects

-- -- U₀-is-inj : (A : ℤAlg 𝓤) (B : ℤAlg 𝓥) → U₀ A ≡ U₀ B ≃ A ≡ B
-- -- U₀-is-inj = ?

-- -- U is Fully Faithful

-- U-is-FF : ⦃ fe : FunExt ⦄ ⦃ univ : Univalence ⦄ (A : ℤAlg 𝓤) (B : ℤAlg 𝓥) → ℤHom A B ≃ ℕHom (U₀ A) (U₀ B)
-- U-is-FF (A , a₀ , s , s-is-hae) (B , b₀ , s' , s'-is-hae) = Σ-assoc _ _ _ ● Σ-preserves-family-≃ (Σ-induction (λ f q → simple-homs A A (s , s-is-hae) B B (s' , s'-is-hae) f f)) ● ≃-sym (Σ-assoc _ _ _)



-- -- IV. Fibered ℕ- and ℤ-Algebras

-- FibℕAlg : (𝓥 : Universe) → ℕAlg 𝓤 → 𝓤 ⊔ (𝓥 ⁺) ̇
-- FibℕAlg 𝓥 (A , a₀ , s) = Σ E ꞉ (A → 𝓥 ̇) , E a₀ × ((a : A) → E a → E (s a))






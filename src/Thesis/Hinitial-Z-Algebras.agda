{-# OPTIONS --without-K --exact-split --safe #-}

open import Ch1.Type-theory
open import Ch2.Homotopy-type-theory
open import Ch3.Sets-and-logic
open import Ch4.Equivalences
open import Thesis.Z-Algebras
open import Thesis.Identity-types

module Thesis.Hinitial-Z-Algebras where


-- I. Identity Type of Algebras

isiso : (A : Alg 𝓤) (B : Alg 𝓥) → Hom A B → 𝓤 ⊔ 𝓥 ̇
isiso A B f = Σ g ꞉ Hom B A , (comp B A B f g ≡ algid B) × (comp A B A g f ≡ algid A)

_≅_ : Alg 𝓤 → Alg 𝓥 → 𝓤 ⊔ 𝓥 ̇
A ≅ B = Σ f ꞉ Hom A B , isiso A B f

isiso-to-isequiv : ⦃ fe : FunExt ⦄ (A : Alg 𝓤) (B : Alg 𝓥) (f : Hom A B) → isiso A B f → isequiv (pr₁ f)
isiso-to-isequiv A B f (g , qfg , qgf) = qinv-to-isequiv (pr₁ g , pr₁ (Hom-≡-elim B B _ _ qfg) , pr₁ (Hom-≡-elim A A _ _ qgf))

AlgId : Alg 𝓤 → Alg 𝓥 → 𝓤 ⊔ 𝓥 ̇
AlgId (A , Str-A) (B , Str-B) = Σ e ꞉ A ≃ B , HomStr (A , Str-A) (B , Str-B) (pr₁ e)

module _ (univ : Univalence) where

  open Full-Univalence univ

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


-- II. Initial Algebras

ishinit : (𝓥 : Universe) → Alg 𝓤 → 𝓤 ⊔ 𝓥 ⁺ ̇
ishinit 𝓥 A = (B : Alg 𝓥) → isContr (Hom A B)

ishinit-is-Prop : ⦃ fe : FunExt ⦄ (𝓥 : Universe) (A : Alg 𝓤) → isProp (ishinit 𝓥 A)
ishinit-is-Prop 𝓥 A = Π-preserves-Props _ (λ B → isContr-is-Prop _)

hasrec : (𝓥 : Universe) → Alg 𝓤 → 𝓤 ⊔ 𝓥 ⁺ ̇
hasrec 𝓥 A = (B : Alg 𝓥) → Hom A B

hasrecunique : (𝓥 : Universe) (A : Alg 𝓤) → 𝓤 ⊔ 𝓥 ⁺ ̇
hasrecunique 𝓥 A = (B : Alg 𝓥) → isProp (Hom A B)

ishinit-is-rec&unique : ⦃ fe : FunExt ⦄ (𝓥 : Universe) (A : Alg 𝓤) → ishinit 𝓥 A ≃ (hasrec 𝓥 A × hasrecunique 𝓥 A) 
ishinit-is-rec&unique {𝓤} 𝓥 A = ⇔-to-≃ (ishinit-is-Prop 𝓥 A) rec&unique-is-Prop (ishinit-to-rec&unique , rec&unique-to-ishinit)
  where
  rec&unique-is-Prop : isProp (hasrec 𝓥 A × hasrecunique 𝓥 A)
  rec&unique-is-Prop (rec , η) (rec' , η') = inv ×-≡-≃ ((funext (λ B → η B _ _)) , Π-preserves-Props _ (λ B → isProp-is-Prop _) _ _)
  ishinit-to-rec&unique : ishinit 𝓥 A → hasrec 𝓥 A × hasrecunique 𝓥 A
  ishinit-to-rec&unique A-init = (λ B → pr₁ (A-init B)) , (λ B → isContr-to-isProp (A-init B))
  rec&unique-to-ishinit : hasrec 𝓥 A × hasrecunique 𝓥 A → ishinit 𝓥 A
  rec&unique-to-ishinit (rec , η) B = (rec B) , (η B (rec B))

rec&unique-to-ishinit : ⦃ fe : FunExt ⦄ (𝓥 : Universe) (A : Alg 𝓤) → hasrec 𝓥 A × hasrecunique 𝓥 A → ishinit 𝓥 A
rec&unique-to-ishinit 𝓥 A = inv (ishinit-is-rec&unique 𝓥 A) 

InitAlg : (𝓤 : Universe) → 𝓤 ⁺ ̇
InitAlg 𝓤 = Σ A ꞉ Alg 𝓤 , ishinit 𝓤 A

InitAlg-is-Prop : (univ : Univalence) (𝓤 : Universe) → isProp (InitAlg 𝓤)
InitAlg-is-Prop univ 𝓤 (A , A-init) (B , B-init)  = Σ-over-predicate (ishinit-is-Prop 𝓤) (≅-to-≡ univ A B (
  pr₁ (A-init B) ,
  pr₁ (B-init A) ,
  isContr-to-isProp (B-init B) _ _ ,
  isContr-to-isProp (A-init A) _ _
  ))
  where open Full-Univalence univ

≅-is-Contr : (A B : InitAlg 𝓤) → isContr (pr₁ A ≅ pr₁ B)
≅-is-Contr (A , A-init) (B , B-init) = ≃-preserves-Contr (≃-sym (Σ-over-Contr-base-is-fib (Hom A B) (isiso A B) (A-init B) ● Σ-over-Contr-base-is-fib (Hom B A) _ (B-init A))) (×-preserves-Contr _ _ (pr₁ Prop-iff-Contr-≡ (pr₂ (pr₁ isContr-iff-is-inhabited-Prop (B-init B))) _ _) (pr₁ Prop-iff-Contr-≡ (pr₂ (pr₁ isContr-iff-is-inhabited-Prop (A-init A))) _ _))
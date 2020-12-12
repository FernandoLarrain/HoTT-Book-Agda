{-# OPTIONS --without-K --exact-split #-}

open import Ch1.Type-theory
open import Ch2.Homotopy-type-theory
open import Ch3.Sets-and-logic
open import Ch4.Equivalences

module Thesis.WildCats

 -- Fix a universe
  
 (𝓤 : Universe)

 -- Fix a wild cat

 (Obj : 𝓤 ̇)
 (Hom : Obj → Obj → 𝓤 ̇)
 (_·_ : {A B C : Obj} → Hom B C → Hom A B → Hom A C) 
 (ide : (A : Obj) → Hom A A)
 (assoc : {A B C D : Obj} (h : Hom C D) (g : Hom B C) (f : Hom A B) → h · (g · f) ≡ (h · g) · f)
 (run : {A B : Obj} (f : Hom A B) → f · ide A ≡ f)
 (lun : {A B : Obj} (f : Hom A B) → ide B · f ≡ f)

 -- with binary products

 (prod : Obj → Obj → Obj)
 (p₁ : {A B : Obj} → Hom (prod A B) A)
 (p₂ : {A B : Obj} → Hom (prod A B) B)
 (prod-UMP : (A B X : Obj) → isequiv {_} {_} {Hom X (prod A B)} {Hom X A × Hom X B} λ f → (p₁ · f) , (p₂ · f))

 -- and equalizers

 (eq : {A B : Obj} → Hom A B → Hom A B → Obj)
 (m : {A B : Obj} (f g : Hom A B) → Hom (eq f g) A)
 (meq : {A B : Obj} (f g : Hom A B) → f · m f g  ≡ g · m f g)
 (eq-UMP : (A B X : Obj) (f g : Hom A B) → isequiv {_} {_} {Hom X (eq f g)} {Σ h ꞉ Hom X A , f · h ≡ g · h} λ u → (m f g · u) , (assoc _ _ _ ∙ ap (_· u) (meq f g) ∙ assoc _ _ _ ⁻¹))

 where

-- -- unique map into product

-- prod! : {A B X : Obj} → Hom X A → Hom X B → Hom X (prod A B)
-- prod! {A} {B} {X} f g = isequiv₁ (prod-UMP A B X) (f , g)

-- -- unique map into equalizer

-- eq! : {A B X : Obj} (f g : Hom A B) (h : Hom X A) → f · h ≡ g · h → Hom X (eq f g)
-- eq! {A} {B} {X} f g h p = isequiv₁ (eq-UMP A B X f g) (h , p) 

-- the theorem

ishinit : Obj → 𝓤 ̇
ishinit A = (B : Obj) → isContr (Hom A B)

isind : Obj → 𝓤 ̇
isind A = (B : Obj) (f : Hom B A) → Σ g ꞉ Hom A B , f · g ≡ ide A

ishinit-to-isind : (A : Obj) → ishinit A → isind A
ishinit-to-isind A A-hinit B f = (pr₁ (A-hinit B)) , (isContr-to-isProp (A-hinit A) _ _)

isind-to-ishinit : (A : Obj) → isind A → ishinit A
isind-to-ishinit A A-ind B with A-ind (prod A B) p₁
... | (p₁⁻¹ , q) = f , contraction
  where
  f : Hom A B
  f = p₂ · p₁⁻¹
  contraction : (g : Hom A B) → f ≡ g
  contraction g with A-ind (eq f g) (m f g)
  ... | (m⁻¹ , q') = run _ ⁻¹ ∙ ap (f ·_) (q' ⁻¹) ∙ assoc _ _ _ ∙ ap (_· m⁻¹) (meq f g) ∙ assoc _ _ _ ⁻¹ ∙ (ap (g ·_) q' ∙ run _)

ishinit-is-Prop : (A : Obj) → isProp (ishinit A)
ishinit-is-Prop A = Π-preserves-Props _ (λ A → isContr-is-Prop _)

uniqueness-pple : (A : Obj) → isind A → (B : Obj) (f : Hom B A) → isProp (Σ g ꞉ Hom A B , f · g ≡ ide A)
uniqueness-pple A A-ind B f (g , p) (h , q) =
  let A-hinit = isind-to-ishinit A A-ind
  in dpair-≡ (isContr-to-isProp (A-hinit B) _ _ , isContr-to-isProp (pr₁ Prop-iff-Contr-≡ (isContr-to-isProp (A-hinit A)) (f · h) (ide A)) _ _)

isind-is-Prop : (A : Obj) → isProp (isind A)
isind-is-Prop A A-ind = aux _
  where
  aux : isProp (isind A)
  aux = Π-preserves-Props _ (λ B → Π-preserves-Props _ (λ f → uniqueness-pple A A-ind B f))

thm : (A : Obj) → ishinit A ≃ isind A
thm A = ⇔-to-≃ (ishinit-is-Prop A) (isind-is-Prop A) ((ishinit-to-isind A) , (isind-to-ishinit A))

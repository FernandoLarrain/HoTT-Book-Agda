{-# OPTIONS --without-K --exact-split --safe #-}

open import Ch1.Type-theory
open import Ch2.Homotopy-type-theory
open import Ch3.1-Sets-and-n-types
open import Ch3.3-Mere-propositions
open import Ch3.6-The-logic-of-mere-props

module Ch3.11-Contractibility where


-- Definition 3.11.1 (Contractible).

isContr : 𝓤 ̇  → 𝓤 ̇
isContr A = Σ a ꞉ A , (Π x ꞉ A , (a ≡ x))


-- Lemma 3.11.3 (Contractible iff inhabited proposition iff 𝟙).

isContr-to-isProp : {A : 𝓤 ̇} → isContr A → isProp A
isContr-to-isProp (a , c) x y = c x ⁻¹ ∙ c y 

inhabited-Prop-to-isContr : {A : 𝓤 ̇} → A → isProp A → isContr A
inhabited-Prop-to-isContr a i = a , i a

isContr-iff-is-inhabited-Prop : {A : 𝓤 ̇} → (isContr A ⇔ (A × isProp A))
isContr-iff-is-inhabited-Prop {𝓤} {A} = sufficiency , necessity where
  sufficiency : isContr A → A × isProp A
  sufficiency = pair (pr₁ , isContr-to-isProp)
  necessity : A × isProp A → isContr A
  necessity = Σ-induction inhabited-Prop-to-isContr

is-inhabited-Prop-iff-is-𝟙 : {A : 𝓤 ̇} → ((A × isProp A) ⇔ (A ≃ 𝟙))
is-inhabited-Prop-iff-is-𝟙 {𝓤} {A} = sufficiency , necessity where
  sufficiency : A × isProp A → A ≃ 𝟙
  sufficiency (a , i) = inhabited-Prop-is-𝟙 i a
  necessity : A ≃ 𝟙 → A × isProp A
  necessity (f , i) with isequiv-to-qinv i
  ... | (f⁻¹ , β , α) = 
    inv (f , i) ⋆ ,
    λ x y → α x ⁻¹ ∙ ap f⁻¹ (𝟙-is-Prop _ _) ∙ α y

isContr-iff-is-𝟙 : {A : 𝓤 ̇} → (isContr A ⇔ (A ≃ 𝟙))
isContr-iff-is-𝟙 {𝓤} {A} = sufficiency , necessity where
  sufficiency = pr₁ is-inhabited-Prop-iff-is-𝟙 ∘ pr₁ isContr-iff-is-inhabited-Prop
  necessity =  pr₂ isContr-iff-is-inhabited-Prop ∘ pr₂ is-inhabited-Prop-iff-is-𝟙

-- Corollary

≃-of-Contr-types : (A : 𝓤 ̇) (B : 𝓥 ̇) → isContr A → isContr B → A ≃ B
≃-of-Contr-types A B A-is-Contr B-is-Contr = pr₁ isContr-iff-is-𝟙 A-is-Contr ● ≃-sym (pr₁ isContr-iff-is-𝟙 B-is-Contr)

-- Related result: every map between contractible types is an equivalence.

map-between-Contrs-is-equiv : {A : 𝓤 ̇} {B : 𝓥 ̇} (f : A → B) → isContr A → isContr B → isequiv f
map-between-Contrs-is-equiv f (a , i) (b , j) = qinv-to-isequiv ((λ y → a) , (isContr-to-isProp (b , j) (f a)) , i)

-- Related result: a proposition is contractible iff it is inhabited.

isProp-to-isContr-iff-is-inhabited : {A : 𝓤 ̇} → isProp A → isContr A ⇔ A
isProp-to-isContr-iff-is-inhabited A-is-Prop = pr₁ , (λ a → a , A-is-Prop a)

-- Related result: contractible (a.k.a. singleton) types have an induction principle akin to 𝟙-induction, namely singleton induction.

singleton-ind : {A : 𝓤 ̇} (c : isContr A) (P : A → 𝓥 ̇) → P (pr₁ c) → (x : A) → P x
singleton-ind (center , contraction) P u x = transport P (contraction x) u

center-prop-β : {A : 𝓤 ̇} (c : isContr A) (P : A → 𝓥 ̇) (u : P (pr₁ c)) → singleton-ind c P u (pr₁ c) ≡ u
center-prop-β {𝓤} {𝓥} {A} (center , contraction) P u = ap (λ - → transport P - u) (A-is-Set _ _ (contraction center) (refl center)) where
  A-is-Set : isSet A
  A-is-Set = isProp-to-isSet (isContr-to-isProp (center , contraction))  

singleton-ind' : {A : 𝓤 ̇} (a : A) → isProp A → (P : A → 𝓥 ̇) → P a → (x : A) → P x
singleton-ind' a i P u x = transport P (i a x) u

point-prop-β : {A : 𝓤 ̇} (a : A) (i : isProp A) (P : A → 𝓥 ̇) (u : P a) → singleton-ind' a i P u a ≡ u
point-prop-β a i P u = ap (λ - → transport P - u) (isProp-to-isSet i _ _ (i a a) (refl a))


module _ ⦃ fe : FunExt ⦄ where

  -- Lemma 3.11.4 (isContr is a proposition).

  isContr-is-Prop : (A : 𝓤 ̇) → isProp (isContr A)
  isContr-is-Prop A (a , p) (a' , p') =
    dpair-≡ ((p a') ,
    Π-preserves-Props (λ - → a' ≡ -) (Ids-are-Props a') _ p')
    where
      A-is-Prop : isProp A
      A-is-Prop = isContr-to-isProp (a , p)
      Ids-are-Props : (x y : A) → isProp (x ≡ y)
      Ids-are-Props x y = isProp-to-isSet A-is-Prop x y


  -- Corollary 3.11.5 (isContr is contractible when predicated of a contractible type).

  isContr-of-Contr-is-Contr : (A : 𝓤 ̇) → isContr A → isContr (isContr A)
  isContr-of-Contr-is-Contr A c = inhabited-Prop-to-isContr c (isContr-is-Prop A)


  -- Lemma 3.11.6 (Π preserves contractibility).

  Π-preserves-Contr : {A : 𝓤 ̇} (P : A → 𝓥 ̇) → ((x : A) → isContr (P x)) → isContr (Π P)
  Π-preserves-Contr P i =  pr₂ isContr-iff-is-inhabited-Prop ((λ x → pr₁ (i x)) , (Π-preserves-Props P (λ x →  isContr-to-isProp (i x))))

  -- Corollary (→)

  →-preserves-Contr : (A : 𝓤 ̇) (B : 𝓥 ̇) → isContr B → isContr (A → B)
  →-preserves-Contr A B B-is-Contr = Π-preserves-Contr (λ a → B) (λ a → B-is-Contr)


-- Definition of section, retraction and retract.

-- (i) A section is a right inverse, a retraction is a left inverse.

sec : {A : 𝓤 ̇} {B : 𝓥 ̇} → (A → B) → 𝓤 ⊔ 𝓥 ̇   
sec {𝓤} {𝓥} {A} {B} r = Σ s ꞉ (B → A) , r ∘ s ∼ id

ret : {A : 𝓤 ̇} {B : 𝓥 ̇} → (B → A) → 𝓤 ⊔ 𝓥 ̇
ret {𝓤} {𝓥} {A} {B} s = Σ r ꞉ (A → B) , r ∘ s ∼ id

-- (iii) Retracts are codomains of retractions

_◁_ : (B : 𝓥 ̇) (A : 𝓤 ̇) → (𝓤 ⊔ 𝓥) ̇
B ◁ A = Σ r ꞉ (A → B) , (sec r)

retraction : {B : 𝓥 ̇} {A : 𝓤 ̇} → B ◁ A → A → B
retraction (r , s , α) = r

section : {B : 𝓥 ̇} {A : 𝓤 ̇} → B ◁ A → B → A
section (r , s , α) = s

retract-eqn : {B : 𝓥 ̇} {A : 𝓤 ̇} → (ρ : B ◁ A) → retraction ρ ∘ section ρ ∼ id
retract-eqn (r , s , α) = α

-- Remark : equivalences are retractions

≃-to-◁ : {A : 𝓤 ̇} {B : 𝓥 ̇} → A ≃ B → B ◁ A
≃-to-◁ (f , i) = let q = isequiv-to-qinv i in f , qinv₁ q , qinv₂ q


-- Lemma 3.11.7 (Retractions preserve contractibility).

retract-of-Contr-is-Contr : {B : 𝓥 ̇} {A : 𝓤 ̇} → B ◁ A → isContr A → isContr B
retract-of-Contr-is-Contr (r , (s , ε)) (a₀ , c) = center , contraction where
  center = r a₀
  contraction = λ b →
    r a₀
      ≡⟨ ap r (c (s b)) ⟩
    r (s b)
      ≡⟨ ε b ⟩
    b ∎

≃-preserves-Contr : {A : 𝓤 ̇} {B : 𝓥 ̇} → A ≃ B → isContr A → isContr B
≃-preserves-Contr e A-is-Contr = retract-of-Contr-is-Contr (≃-to-◁ e) A-is-Contr


-- Lemma 3.11.8 (The subtype of points equal to a given point is contractible).

free-right-endpt-is-Contr : (A : 𝓤 ̇) (a : A) → isContr (Σ x ꞉ A , (a ≡ x))
free-right-endpt-is-Contr A a = center , contraction
  where
  center = (a , (refl a))
  contraction =  λ z → dpair-≡ (pr₂ z , (transport-post-∙ (pr₂ z) (refl a) ∙ (lu _ ⁻¹)))

free-left-endpt-is-Contr : (A : 𝓤 ̇) (a : A) → isContr (Σ x ꞉ A , (x ≡ a))
free-left-endpt-is-Contr A a = center , contraction 
  where
  center = (a , (refl a)) 
  contraction = λ z → dpair-≡ ((pr₂ z ⁻¹) , (transport-pre-∙ ((pr₂ z) ⁻¹) (refl a) ∙ ((ru _ ⁻¹) ∙ ⁻¹-invol (pr₂ z))))


-- Lemma 3.11.9.

-- (i) The sum of a contractible family of types is the index type.

Σ-of-Contr-family-is-base : (A : 𝓤 ̇)  (P : A → 𝓥 ̇) → ((x : A) → isContr (P x)) → Σ P ≃ A
Σ-of-Contr-family-is-base A P c = pr₁ , (qinv-to-isequiv ((λ x → x , pr₁ (c x)) , (refl , λ z → dpair-≡ (refl _ , pr₂ (c (pr₁ z)) (pr₂ z)))))

Σ-over-𝟙 : (P : 𝟙 → 𝓤 ̇) → Σ P ≃ P ⋆
Σ-over-𝟙 P = Σ-induction (𝟙-induction _ id) , qinv-to-isequiv ((λ x → ⋆ , x) , hrefl _ , Σ-induction (𝟙-induction _ (hrefl _)))

-- (ii) The sum over a contractible base is the fiber at the center of the base.

Σ-over-Contr-base-is-fib : (A : 𝓤 ̇) (P : A → 𝓥 ̇) → (c : isContr A) → Σ P ≃ P (pr₁ c)
Σ-over-Contr-base-is-fib A P (a , i) = f , (qinv-to-isequiv (f⁻¹ , (α , β))) where
  f : Σ P → P a
  f (x , y) = transport P (i x ⁻¹) y
  f⁻¹ : P a → Σ P
  f⁻¹ y = a , y
  α : f ∘ f⁻¹ ∼ id
  α y = ap (λ - → transport P - y) (A-is-Set a a (i a ⁻¹) (refl _))
    where
    A-is-Set : isSet A
    A-is-Set = isProp-to-isSet (isContr-to-isProp (a , i))
  β : f⁻¹ ∘ f ∼ id
  β (x , y) = dpair-≡ (i x , (
    transport P (i x) (transport P (i x ⁻¹) y)
      ≡⟨ transport-∙ P (i x ⁻¹) (i x) y ⟩
    transport P ((i x ⁻¹) ∙ i x) y
      ≡⟨ ap (λ - → transport P - y) (linv (i x)) ⟩
    y ∎))

Π-over-Contr-base-is-fib : ⦃ fe : FunExt ⦄ (A : 𝓤 ̇) (P : A → 𝓥 ̇) → (c : isContr A) → Π P ≃ P (pr₁ c)
Π-over-Contr-base-is-fib A P (a , i) =
  (λ f → f a) ,
  qinv-to-isequiv (
    (λ b x → transport P (i x) b) ,
    (λ b → ap (λ - → transport P - b) (A-is-Set a a (i a) (refl a))) ,
    λ f → funext λ x → apd f (i x)
    )
  where
  A-is-Set : isSet A
  A-is-Set = isProp-to-isSet (isContr-to-isProp (a , i))
  
-- (iii) Corollaries

Σ-preserves-Contr : {A : 𝓤 ̇} {P : A → 𝓥 ̇} → isContr A → ((x : A) → isContr (P x)) → isContr (Σ P)
Σ-preserves-Contr A-is-Contr P-is-Contr-family = retract-of-Contr-is-Contr (≃-to-◁ (≃-sym (Σ-of-Contr-family-is-base _ _ P-is-Contr-family))) A-is-Contr 

×-preserves-Contr : (A : 𝓤 ̇) (B : 𝓥 ̇) → isContr A → isContr B → isContr (A × B)
×-preserves-Contr A B A-is-Contr B-is-Contr = Σ-preserves-Contr A-is-Contr (λ a → B-is-Contr)


-- Lemma 3.11.10 (A type is a proposition iff its path-spaces are contractible).

Prop-iff-Contr-≡ : {A : 𝓤 ̇} → (isProp A ⇔ ((x y : A) → isContr (x ≡ y)))
Prop-iff-Contr-≡ {𝓤} {A} = sufficiency , necessity where
  sufficiency : isProp A → (x y : A) → isContr (x ≡ y)
  sufficiency i x y = (i x y) , (isProp-to-isSet i x y (i x y))
  necessity : ((x y : A) → isContr (x ≡ y)) → isProp A
  necessity f x y = pr₁ (f x y)

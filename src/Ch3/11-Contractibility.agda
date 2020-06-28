{-# OPTIONS --without-K --exact-split #-}

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

isContr-iff-is-inhabited-Prop : (A : 𝓤 ̇ ) → (isContr A → A × isProp A) × (A × isProp A → isContr A)
isContr-iff-is-inhabited-Prop A = sufficiency , necessity where
  sufficiency : isContr A → A × isProp A
  sufficiency (a , c) = a , λ x y → c x ⁻¹ ∙ c y
  necessity : A × isProp A → isContr A
  necessity (a , i) = a , λ x → i a x

is-inhabited-Prop-iff-is-𝟙 : (A : 𝓤 ̇ ) → (A × isProp A → A ≃ 𝟙) × (A ≃ 𝟙 → A × isProp A)
is-inhabited-Prop-iff-is-𝟙 A = sufficiency , necessity where
  sufficiency : A × isProp A → A ≃ 𝟙
  sufficiency (a , i) = inhabited-Prop-is-𝟙 A i a
  necessity : A ≃ 𝟙 → A × isProp A
  necessity e = 
    pr₁ (≃-sym e) ⋆ ,
    λ x y →
      x
        ≡⟨ α x ⁻¹ ⟩
      f⁻¹ (f x)
        ≡⟨ ap f⁻¹ (𝟙-is-Prop _ _) ⟩
      f⁻¹ (f y)
        ≡⟨ α y ⟩
      y ∎
    where
      f = pr₁ e
      i = pr₂ e
      q = isequiv-to-qinv i
      f⁻¹ = qinv₁ q
      α = qinv₃ q

isContr-iff-is-𝟙 : (A : 𝓤 ̇) → (isContr A → A ≃ 𝟙) × (A ≃ 𝟙 → isContr A)
isContr-iff-is-𝟙 A = sufficiency , necessity where
  sufficiency = pr₁ (is-inhabited-Prop-iff-is-𝟙 A) ∘ pr₁ (isContr-iff-is-inhabited-Prop A)
  necessity =  pr₂ (isContr-iff-is-inhabited-Prop A) ∘ pr₂ (is-inhabited-Prop-iff-is-𝟙 A)


-- Lemma 3.11.4 (isContr is a proposition).

isContr-is-Prop : (A : 𝓤 ̇ ) → isProp (isContr A)
isContr-is-Prop A (a , p) (a' , p') =
  dpair-≡ ((p a') ,
  Π-preserves-Props (λ - → a' ≡ -) (Ids-are-Props a') _ p')
  where
    A-is-Prop : isProp A
    A-is-Prop = pr₂ (pr₁ (isContr-iff-is-inhabited-Prop A) (a , p))
    Ids-are-Props : (x y : A) → isProp (x ≡ y)
    Ids-are-Props x y = Props-are-Sets A A-is-Prop x y


-- Corollary 3.11.5 (isContr is contractible when predicated of a contractible type).

isContr-of-Contr-is-Contr : (A : 𝓤 ̇ ) → isContr A → isContr (isContr A)
isContr-of-Contr-is-Contr A c = pr₂ (isContr-iff-is-inhabited-Prop (isContr A)) (c , (isContr-is-Prop A))


-- Lemma 3.11.6 (Π preserves contractibility).

Π-preserves-Contr : {A : 𝓤 ̇ } (P : A → 𝓥 ̇ ) → ((x : A) → isContr (P x)) → isContr (Π P)
Π-preserves-Contr P i =  pr₂ (isContr-iff-is-inhabited-Prop (Π P)) ((λ x → pr₁ (i x)) , (Π-preserves-Props P (λ x → pr₂ (pr₁ (isContr-iff-is-inhabited-Prop (P x)) (i x)))))

-- Corollary (→)
  
→-preserves-Contr : (A : 𝓤 ̇) (B : 𝓥 ̇) → isContr B → isContr (A → B)
→-preserves-Contr A B B-is-Contr = Π-preserves-Contr (λ a → B) (λ a → B-is-Contr)


-- Definition of section, retraction and retract.

-- (i) A section is a right inverse

has-section : {A : 𝓤 ̇} {B : 𝓥 ̇} → (A → B) → 𝓤 ⊔ 𝓥 ̇   
has-section {A = A} {B} r = Σ s ꞉ (B → A) , r ∘ s ∼ id

-- (ii) A retraction is a right-invertible function

is-retraction : {A : 𝓤 ̇} {B : 𝓥 ̇} (r : A → B) → (𝓤 ⊔ 𝓥) ̇
is-retraction {A = A} {B} r = has-section r

-- (iii) Retracts are codomains of retractions

_◁_ : (B : 𝓥 ̇) (A : 𝓤 ̇) → (𝓤 ⊔ 𝓥) ̇
B ◁ A = Σ r ꞉ (A → B) , (is-retraction r)

retraction : {B : 𝓥 ̇} {A : 𝓤 ̇} → B ◁ A → A → B
retraction (r , s , α) = r

section : {B : 𝓥 ̇} {A : 𝓤 ̇} → B ◁ A → B → A
section (r , s , α) = s

retraction-eqn : {B : 𝓥 ̇} {A : 𝓤 ̇} → (ρ : B ◁ A) → retraction ρ ∘ section ρ ∼ id
retraction-eqn (r , s , α) = α

-- Remark

≃-to-◁ : {A : 𝓤 ̇} {B : 𝓥 ̇} → A ≃ B → B ◁ A
≃-to-◁ (f , i) = f , qinv₁ q , qinv₂ q where
  q = isequiv-to-qinv i


-- Lemma 3.11.7 (Retractions preserve contractibility).

retract-of-Contr-is-Contr : {B : 𝓥 ̇ } {A : 𝓤 ̇} → B ◁ A → isContr A → isContr B
retract-of-Contr-is-Contr (r , (s , ε)) (a₀ , c) = center , centrality where
  center = r a₀
  centrality = λ b →
    r a₀
      ≡⟨ ap r (c (s b)) ⟩
    r (s b)
      ≡⟨ ε b ⟩
    b ∎


-- Lemma 3.11.8 (The subtype of points equal to a given point is contractible).

free-right-endpt-is-Contr : (A : 𝓤 ̇ ) (a : A) → isContr (Σ x ꞉ A , (a ≡ x))
free-right-endpt-is-Contr A a = center , centrality
  where
  center = (a , (refl a))
  centrality =  λ z → dpair-≡ (pr₂ z , (transport-post-∙ A a _ _ (pr₂ z) (refl a) ∙ (lu _ ⁻¹)))

free-left-endpt-is-Contr : (A : 𝓤 ̇ ) (a : A) → isContr (Σ x ꞉ A , (x ≡ a))
free-left-endpt-is-Contr A a = center , centrality 
  where
  center = (a , (refl a)) 
  centrality = λ z → dpair-≡ ((pr₂ z ⁻¹) , (transport-pre-∙ A a _ _ ((pr₂ z) ⁻¹) (refl a) ∙ ((ru _ ⁻¹) ∙ ⁻¹-invol (pr₂ z))))


-- Lemma 3.11.9.

-- (i) The sum of a contractible family of types is the index type.

Σ-of-Contr-family-is-base : (A : 𝓤 ̇)  (P : A → 𝓥 ̇ ) → ((x : A) → isContr (P x)) → Σ P ≃ A
Σ-of-Contr-family-is-base A P c = pr₁ , (qinv-to-isequiv ((λ x → x , pr₁ (c x)) , (refl , λ z → dpair-≡ (refl _ , pr₂ (c (pr₁ z)) (pr₂ z)))))

-- (ii) The sum over a contractible base is the fiber at the center of the base.

Σ-over-Contr-base-is-fib : (A : 𝓤 ̇) (P : A → 𝓥 ̇ ) → (c : isContr A) → Σ P ≃ P (pr₁ c)
Σ-over-Contr-base-is-fib A P (a , i) = f , (qinv-to-isequiv (f⁻¹ , (α , β))) where
  f : Σ P → P a
  f (x , y) = transport P (i x ⁻¹) y
  f⁻¹ : P a → Σ P
  f⁻¹ y = a , y
  α : f ∘ f⁻¹ ∼ id
  α y = ap (λ - → transport P - y) (A-is-Set a a (i a ⁻¹) (refl _))
    where
    A-is-Set : isSet A
    A-is-Set = Props-are-Sets A (pr₂ (pr₁ (isContr-iff-is-inhabited-Prop A) (a , i)))
  β : f⁻¹ ∘ f ∼ id
  β (x , y) = dpair-≡ (i x , (
    transport P (i x) (transport P (i x ⁻¹) y)
      ≡⟨ transport-∙ P (i x ⁻¹) (i x) y ⟩
    transport P ((i x ⁻¹) ∙ i x) y
      ≡⟨ ap (λ - → transport P - y) (linv (i x)) ⟩
    y ∎))

Π-over-Contr-base-is-fib : (A : 𝓤 ̇) (P : A → 𝓥 ̇) → (c : isContr A) → Π P ≃ P (pr₁ c)
Π-over-Contr-base-is-fib A P (a , i) =
  (λ f → f a) ,
  qinv-to-isequiv (
    (λ b x → transport P (i x) b) ,
    (λ b → ap (λ - → transport P - b) (A-is-Set a a (i a) (refl a))) ,
    λ f → funext _ _ λ x → apd f (i x)
    )
  where
  A-is-Set : isSet A
  A-is-Set = Props-are-Sets A (pr₂ (pr₁ (isContr-iff-is-inhabited-Prop A) (a , i)))
  
-- (iii) Corollaries

Σ-preserves-Contr : (A : 𝓤 ̇) (P : A → 𝓥 ̇ ) → isContr A → ((x : A) → isContr (P x)) → isContr (Σ P)
Σ-preserves-Contr A P A-is-Contr P-is-Contr = retract-of-Contr-is-Contr (≃-to-◁ (≃-sym (Σ-of-Contr-family-is-base A P P-is-Contr))) A-is-Contr 

×-preserves-Contr : (A : 𝓤 ̇) (B : 𝓥 ̇) → isContr A → isContr B → isContr (A × B)
×-preserves-Contr A B A-is-Contr B-is-Contr = Σ-preserves-Contr A (λ a → B) A-is-Contr (λ a → B-is-Contr)


-- Lemma 3.11.10 (A type is a proposition iff its path-space is contractible).

Prop-iff-Contr-≡ : (A : 𝓤 ̇ ) → (isProp A → ((x y : A) → isContr (x ≡ y))) × (((x y : A) → isContr (x ≡ y)) → isProp A)
Prop-iff-Contr-≡ A = sufficiency , necessity where
  sufficiency : isProp A → (x y : A) → isContr (x ≡ y)
  sufficiency i x y = (i x y) , ((Props-are-Sets A i) x y (i x y))
  necessity : ((x y : A) → isContr (x ≡ y)) → isProp A
  necessity f x y = pr₁ (f x y)


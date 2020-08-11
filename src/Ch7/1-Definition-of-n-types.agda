{-# OPTIONS --without-K --exact-split --safe #-}

open import Ch1.Type-theory
open import Ch2.Homotopy-type-theory
open import Ch3.Sets-and-logic
open import Ch4.Equivalences

module Ch7.1-Definition-of-n-types where


-- Definition of truncation levels

data Tlevel : 𝓤₀ ̇ where
  ⟨-2⟩ : Tlevel
  S : Tlevel → Tlevel

⟨-1⟩ : Tlevel
⟨-1⟩ = S ⟨-2⟩

⟨0⟩ : Tlevel
⟨0⟩ = S ⟨-1⟩

⟨1⟩ : Tlevel
⟨1⟩ = S ⟨0⟩


-- Tlevel is equivalent to ℕ

to-ℕ : Tlevel → ℕ
to-ℕ ⟨-2⟩ = zero
to-ℕ (S n) = succ (to-ℕ n)

from-ℕ : ℕ → Tlevel
from-ℕ zero = ⟨-2⟩
from-ℕ (succ m) = S (from-ℕ m)

to-ℕ-from-ℕ-is-id : from-ℕ ∘ to-ℕ ∼ 𝑖𝑑 _
to-ℕ-from-ℕ-is-id ⟨-2⟩ = refl _
to-ℕ-from-ℕ-is-id (S n) = ap S (to-ℕ-from-ℕ-is-id n)

from-ℕ-to-ℕ-is-id : to-ℕ ∘ from-ℕ ∼ 𝑖𝑑 _
from-ℕ-to-ℕ-is-id zero = refl _
from-ℕ-to-ℕ-is-id (succ m) = ap succ (from-ℕ-to-ℕ-is-id m)

Tlevel-≃-ℕ : Tlevel ≃ ℕ
Tlevel-≃-ℕ = to-ℕ , (qinv-to-isequiv (from-ℕ , (from-ℕ-to-ℕ-is-id , to-ℕ-from-ℕ-is-id)))

Tlevel-is-Set : isSet Tlevel
Tlevel-is-Set = ≃-preserves-Sets (≃-sym Tlevel-≃-ℕ) ℕ-is-Set


-- Inclusion of ℕ in Tlevel

⟨_⟩ : ℕ → Tlevel
⟨ 0 ⟩ = ⟨0⟩
⟨ succ n ⟩ = S ⟨ n ⟩


-- Definition 7.1.1 (Is-n-type).

is_type_ : Tlevel → 𝓤 ̇ → 𝓤 ̇
is ⟨-2⟩ type X = isContr X
is S n type X = (x y : X) → is n type (x ≡ y)


-- Theorem 7.1.4 (Retractions preserve truncation level).

retractions-preserve-Tlevel : (n : Tlevel) (Y : 𝓥 ̇) (X : 𝓤 ̇) → Y ◁ X → is n type X → is n type Y  
retractions-preserve-Tlevel ⟨-2⟩ Y X = retract-of-Contr-is-Contr {B = Y} {X} 
retractions-preserve-Tlevel (S n) Y X (p , s , ε) X-is-Sn-type y y' = retractions-preserve-Tlevel n (y ≡ y') (s y ≡ s y') (
  (λ q → ε y ⁻¹ ∙ ap p q ∙ ε y') ,
  (ap s) ,
  λ q →  ap (λ - → ε y ⁻¹ ∙ - ∙ ε y') (ap-∘ s p q) ∙ (hnat' ε q ∙ ap-id _) 
  )
  (X-is-Sn-type (s y) (s y'))


-- Corollary 7.1.5 (Equivalences preserve truncation level).

≃-preserves-Tlevel : (n : Tlevel) (X : 𝓤 ̇) (Y : 𝓥 ̇) → X ≃ Y → is n type X → is n type Y
≃-preserves-Tlevel n X Y e = retractions-preserve-Tlevel n Y X (≃-to-◁ e) 


-- Theorem 7.1.6 (Embeddings pull back higher truncation levels).

embedding-pulls-back-Tlevel : (n : Tlevel) → (X : 𝓤 ̇) (Y : 𝓥 ̇) (f : X → Y) → is-embedding f → is S n type Y → is S n type X
embedding-pulls-back-Tlevel n X Y f emb Y-is-Sn-type x x' = ≃-preserves-Tlevel n (f x ≡ f x') (x ≡ x') (≃-sym (ap f , emb x x')) (Y-is-Sn-type (f x) (f x'))


-- Theorem 7.1.7 (n-types are (n + 1)-types).

cumulativity-of-Tlevels : (n : Tlevel) (X : 𝓤 ̇) → is n type X → is S n type X
cumulativity-of-Tlevels ⟨-2⟩ X (center , centrality) x x' = (centrality x ⁻¹ ∙ centrality x') , (ℍ x (λ x' p → centrality x ⁻¹ ∙ centrality x' ≡ p) (linv _) x')
cumulativity-of-Tlevels (S n) X X-is-Sn-type x x' = cumulativity-of-Tlevels n _ (X-is-Sn-type x x')


-- Theorem 7.1.8 (Σ preserves truncation level of sumands).

Σ-preserves-Tlevel : (n : Tlevel) (A : 𝓤 ̇) (B : A → 𝓥 ̇) → is n type A → ((a : A) → is n type (B a)) → is n type (Σ B)
Σ-preserves-Tlevel ⟨-2⟩ A B = Σ-preserves-Contr 
Σ-preserves-Tlevel (S n) A B A-is-Sn-type B-is-Sn-family (a , b) (a' , b') = ≃-preserves-Tlevel n _ _ (≃-sym Σ-≡-equiv) (Σ-preserves-Tlevel n _ _ (A-is-Sn-type _ _) λ p → B-is-Sn-family _ _ _)


-- Corollaries (× and pb)

×-preserves-Tlevel : (n : Tlevel) (A : 𝓤 ̇) (B : 𝓥 ̇) → is n type A → is n type B → is n type (A × B)
×-preserves-Tlevel n A B A-is-n-type B-is-n-type = Σ-preserves-Tlevel n A (λ a → B) A-is-n-type λ a → B-is-n-type 

pb-preserves-Tlevel : (n : Tlevel) (A : 𝓤 ̇) (B : 𝓥 ̇) (C : 𝓦 ̇) (f : A → C) (g : B → C) → is n type A → is n type B → is n type C → is n type (pb f g)
pb-preserves-Tlevel n A B C f g A-is-n-type B-is-n-type C-is-n-type = Σ-preserves-Tlevel n _ _ A-is-n-type (λ a →
  Σ-preserves-Tlevel n _ _ B-is-n-type (λ b →
    cumulativity-of-Tlevels n _ C-is-n-type (f a) (g b)
    )
  )
  
  
-- Theorem 7.1.9 (Π preserves truncation level).

module _ ⦃ fe : FunExt ⦄ where

  Π-preserves-Tlevel : (n : Tlevel) (A : 𝓤 ̇) (B : A → 𝓥 ̇) → ((a : A) → is n type (B a)) → is n type (Π B)
  Π-preserves-Tlevel ⟨-2⟩ A = Π-preserves-Contr
  Π-preserves-Tlevel (S n) A B B-is-Sn-family f g = ≃-preserves-Tlevel n (f ∼ g) _ (≃-sym (happly , happly-is-equiv)) (Π-preserves-Tlevel n _ _ λ a → B-is-Sn-family _ _ _)

  →-preserves-Tlevel : (n : Tlevel) (A : 𝓤 ̇) (B : 𝓥 ̇) → is n type B → is n type (A → B)
  →-preserves-Tlevel n A B B-is-n-type = Π-preserves-Tlevel n A (λ a → B) (λ a → B-is-n-type) 


-- Theorem 7.1.10 (Truncation level is a predicate).

Tlevel-is-predicate : ⦃ fe : FunExt ⦄ (n : Tlevel) (X : 𝓤 ̇) → isProp (is n type X)
Tlevel-is-predicate ⟨-2⟩ = isContr-is-Prop
Tlevel-is-predicate (S n) X = Π-preserves-Props _ λ x →
  Π-preserves-Props _ λ x' →
    Tlevel-is-predicate n (x ≡ x')


-- Definition of type of all (small) n-Types.

_-Type_ : (n : Tlevel) (𝓤 : Universe) → 𝓤 ⁺ ̇
n -Type 𝓤 = Σ X ꞉ (𝓤 ̇) , is n type X


-- Theorem 7.1.11 (n-Type is an (n + 1)-type).

module _  ⦃ fe : FunExt ⦄ ⦃ univ : Univalence ⦄ where

  Tlevel-Type-is-of-next-Tlevel : (n : Tlevel) → is S n type (n -Type 𝓤)

  -- (i) Irrelevance of Tlevel data.

  irrelevance-of-Tdata : (n : Tlevel) (Y Y' : n -Type 𝓤) → (Y ≡ Y') ≃ (pr₁ Y ≃ pr₁ Y')
  irrelevance-of-Tdata n (X , p) (X' , p') = Σ-over-predicate' (Tlevel-is-predicate n) _ _ ● (idtoeqv , idtoeqv-is-equiv) 

  -- (ii) pr₁ is an embedding.

  pr₁-is-embedding : (X X' : 𝓤 ̇) → is-embedding (pr₁ {X = X → X'} {λ f → isequiv f}) 
  pr₁-is-embedding X X' e e' = pr₂ (Σ-over-predicate' ishae-is-Prop e e')

  -- (iii) The theorem.

  Tlevel-Type-is-of-next-Tlevel ⟨-2⟩ (X , p) (X' , p') = ≃-preserves-Tlevel ⟨-2⟩ (X ≃ X') _ (≃-sym (irrelevance-of-Tdata ⟨-2⟩ _ _)) (pr₂ isContr-iff-is-inhabited-Prop (is-inhabited , is-Prop))
    where
    is-inhabited : X ≃ X'
    is-inhabited = pr₁ isContr-iff-is-𝟙 p ● ≃-sym (pr₁ isContr-iff-is-𝟙 p')
    is-Prop : isProp (X ≃ X')
    is-Prop = (pr₂ Prop-iff-Contr-≡ (embedding-pulls-back-Tlevel ⟨-2⟩ (X ≃ X') (X → X') pr₁ (pr₁-is-embedding X X') (→-preserves-Tlevel (S ⟨-2⟩) X X' (cumulativity-of-Tlevels ⟨-2⟩ _ p'))))

  Tlevel-Type-is-of-next-Tlevel (S n) (X , p) (X' , p') = ≃-preserves-Tlevel (S n) (X ≃ X') _ (≃-sym (irrelevance-of-Tdata (S n) _ _)) (embedding-pulls-back-Tlevel n (X ≃ X') (X → X') pr₁ (pr₁-is-embedding X X') (→-preserves-Tlevel (S n) X X' p'))


-- Translation to old terminology (isContr, isProp, isSet)

isContr-≃-is-⟨-2⟩-type : (A : 𝓤 ̇) → isContr A ≃ is ⟨-2⟩ type A
isContr-≃-is-⟨-2⟩-type A = idtoeqv (refl _)

module _ ⦃ fe : FunExt ⦄ where

  isProp-≃-is-⟨-1⟩-type : (A : 𝓤 ̇) → isProp A ≃ is ⟨-1⟩ type A
  isProp-≃-is-⟨-1⟩-type A = ⇔-to-≃ (isProp-is-Prop _) (Tlevel-is-predicate ⟨-1⟩ A ) Prop-iff-Contr-≡

  isSet-≃-is-⟨0⟩-type : (A : 𝓤 ̇) → isSet A ≃ is ⟨0⟩ type A
  isSet-≃-is-⟨0⟩-type A = ⇔-to-≃ (isSet-is-Prop _) (Tlevel-is-predicate ⟨0⟩ _) ((λ A-is-Set x y → pr₁ (isProp-≃-is-⟨-1⟩-type _) (A-is-Set x y)) , λ A-is-⟨0⟩-type x y → pr₁ (≃-sym (isProp-≃-is-⟨-1⟩-type _)) (A-is-⟨0⟩-type x y))

  -- Retractions preserve propositions

  retractions-preserve-Props : (A : 𝓤 ̇) (B : 𝓥 ̇) → B ◁ A → isProp A → isProp B
  retractions-preserve-Props A B ρ = pr₁ (≃-sym (isProp-≃-is-⟨-1⟩-type B)) ∘ retractions-preserve-Tlevel ⟨-1⟩ B A ρ ∘ pr₁ (isProp-≃-is-⟨-1⟩-type A)

  -- Corollary : retraction of proposition gives equivalence

  retraction-of-Prop-to-≃ : {X : 𝓤 ̇} {Y : 𝓥 ̇} → isProp X → Y ◁ X → X ≃ Y
  retraction-of-Prop-to-≃ {𝓤} {𝓥} {X} {Y} X-is-Prop (r , s , α) = ⇔-to-≃ X-is-Prop (retractions-preserve-Props X Y (r , s , α) X-is-Prop) (r , s)


-- is n type preserves ≃

module _ ⦃ fe : FunExt ⦄ where

  Tlevel-preserves-≃ : (n : Tlevel) {A : 𝓤 ̇} {B : 𝓥 ̇} → A ≃ B → is n type A ≃ is n type B
  Tlevel-preserves-≃ n e = ⇔-to-≃ (Tlevel-is-predicate _ _) (Tlevel-is-predicate _ _) (≃-preserves-Tlevel _ _ _ e , ≃-preserves-Tlevel _ _ _ (≃-sym e))

  isContr-preserves-≃ : {A : 𝓤 ̇} {B : 𝓥 ̇} → A ≃ B → isContr A ≃ isContr B
  isContr-preserves-≃ e = Tlevel-preserves-≃ ⟨-2⟩ e

  isProp-preserves-≃ : {A : 𝓤 ̇} {B : 𝓥 ̇} → A ≃ B → isProp A ≃ isProp B
  isProp-preserves-≃ {𝓤} {𝓥} {A} {B} e = isProp-≃-is-⟨-1⟩-type A ● Tlevel-preserves-≃ ⟨-1⟩ e ● (≃-sym (isProp-≃-is-⟨-1⟩-type B))

  isSet-preserves-≃ : {A : 𝓤 ̇} {B : 𝓥 ̇} → A ≃ B → isSet A ≃ isSet B
  isSet-preserves-≃ {𝓤} {𝓥} {A} {B} e = isSet-≃-is-⟨0⟩-type A ● Tlevel-preserves-≃ ⟨0⟩ e ● (≃-sym (isSet-≃-is-⟨0⟩-type B))


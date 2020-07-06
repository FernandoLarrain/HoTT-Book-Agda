{-# OPTIONS --without-K --exact-split #-}

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

-- Tlevel is equivalent to ℕ

module Tlevel-≃-ℕ where

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

  equivalence : Tlevel ≃ ℕ
  equivalence = to-ℕ , (qinv-to-isequiv (from-ℕ , (from-ℕ-to-ℕ-is-id , to-ℕ-from-ℕ-is-id)))

  S-is-not-⟨-2⟩ : (n : Tlevel) → ¬ (S n ≡ ⟨-2⟩)
  S-is-not-⟨-2⟩ n p = succ-is-not-0 (to-ℕ n) (ap to-ℕ p)


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

embedding-pulls-back-Tlevel' : (n : Tlevel) → ¬ (n ≡ ⟨-2⟩) → (X : 𝓤 ̇) (Y : 𝓥 ̇) (f : X → Y) → is-embedding f → is n type Y → is n type X
embedding-pulls-back-Tlevel' ⟨-2⟩ not⟨-2⟩ = 𝟘-recursion _ (not⟨-2⟩ (refl _)) 
embedding-pulls-back-Tlevel' (S n) not⟨-2⟩ X Y f emb Y-is-Sn-type x x' = ≃-preserves-Tlevel n (f x ≡ f x') _ (≃-sym (ap f , emb x x'))  (Y-is-Sn-type (f x) (f x'))

embedding-pulls-back-Tlevel : (n : Tlevel) → (X : 𝓤 ̇) (Y : 𝓥 ̇) (f : X → Y) → is-embedding f → is S n type Y → is S n type X
embedding-pulls-back-Tlevel n X Y f emb Y-is-Sn-type x x' = ≃-preserves-Tlevel n (f x ≡ f x') (x ≡ x') (≃-sym (ap f , emb x x')) (Y-is-Sn-type (f x) (f x'))


-- Theorem 7.1.7 (n-types are (n + 1)-types).

cumulativity-of-Tlevels : (n : Tlevel) (X : 𝓤 ̇) → is n type X → is S n type X
cumulativity-of-Tlevels ⟨-2⟩ X (center , centrality) x x' = (centrality x ⁻¹ ∙ centrality x') , (ℍ x (λ x' p → centrality x ⁻¹ ∙ centrality x' ≡ p) (linv _) x')
cumulativity-of-Tlevels (S n) X X-is-Sn-type x x' = cumulativity-of-Tlevels n _ (X-is-Sn-type x x')


-- Theorem 7.1.8 (Σ preserves truncation level of sumands).

Σ-preserves-Tlevel : (n : Tlevel) (A : 𝓤 ̇) (B : A → 𝓥 ̇) → is n type A → ((a : A) → is n type (B a)) → is n type (Σ B)
Σ-preserves-Tlevel ⟨-2⟩ = Σ-preserves-Contr -- Alternatively: introduce A, B, A-is-Contr, B-is-Contr-family and then write [≃-preserves-Tlevel ⟨-2⟩ A _ (≃-sym (Σ-of-Contr-family-is-base A B B-is-Contr-family)) A-is-Contr] 
Σ-preserves-Tlevel (S n) A B A-is-Sn-type B-is-Sn-family (a , b) (a' , b') = ≃-preserves-Tlevel n _ _ (≃-sym (Σ-≡-equiv _ _)) (Σ-preserves-Tlevel n _ _ (A-is-Sn-type _ _) λ p → B-is-Sn-family _ _ _)


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

Π-preserves-Tlevel : (n : Tlevel) (A : 𝓤 ̇) (B : A → 𝓥 ̇) → ((a : A) → is n type (B a)) → is n type (Π B)
Π-preserves-Tlevel ⟨-2⟩ A = Π-preserves-Contr
Π-preserves-Tlevel (S n) A B B-is-Sn-family f g = ≃-preserves-Tlevel n (f ∼ g) _ (≃-sym ((happly _ _) , (hfe _ _))) (Π-preserves-Tlevel n _ _ λ a → B-is-Sn-family _ _ _)

→-preserves-Tlevel : (n : Tlevel) (A : 𝓤 ̇) (B : 𝓥 ̇) → is n type B → is n type (A → B)
→-preserves-Tlevel n A B B-is-n-type = Π-preserves-Tlevel n A (λ a → B) (λ a → B-is-n-type) 
  
-- Theorem 7.1.10 (Truncation level is a property).

Tlevel-is-property : (n : Tlevel) (X : 𝓤 ̇) → isProp (is n type X)
Tlevel-is-property ⟨-2⟩ = isContr-is-Prop
Tlevel-is-property (S n) X = Π-preserves-Props _ λ x →
  Π-preserves-Props _ λ x' →
    Tlevel-is-property n (x ≡ x')


-- Definition of type of all (small) n-Types.

_-Type_ : (n : Tlevel) (𝓤 : Universe) → 𝓤 ⁺ ̇
n -Type 𝓤 = Σ X ꞉ (𝓤 ̇) , is n type X


-- Theorem 7.1.11 (n-Type is an (n + 1)-type).

-- (i) Irrelevance of Tlevel data.
  
irrelevance-of-Tdata : (n : Tlevel) (Y Y' : n -Type 𝓤) → (Y ≡ Y') ≃ (pr₁ Y ≃ pr₁ Y')
irrelevance-of-Tdata n (X , p) (X' , p') = Σ-over-predicate' _ _ (Tlevel-is-property n) _ _ ● ((idtoeqv X X') , (univ _ _ _)) 

-- (ii) pr₁ is an embedding.

pr₁-is-embedding : (X X' : 𝓤 ̇) → is-embedding (pr₁ {X = X → X'} {λ f → isequiv f}) 
pr₁-is-embedding X X' e e' = pr₂ (Σ-over-predicate' _ _ ishae-is-Prop e e')

-- (iii) The theorem.

Tlevel-Type-if-of-next-Tlevel : (n : Tlevel) → is S n type (n -Type 𝓤)

Tlevel-Type-if-of-next-Tlevel ⟨-2⟩ (X , p) (X' , p') = ≃-preserves-Tlevel ⟨-2⟩ (X ≃ X') _ (≃-sym (irrelevance-of-Tdata ⟨-2⟩ _ _)) (pr₂ (isContr-iff-is-inhabited-Prop (X ≃ X')) (is-inhabited , is-Prop))
  where
  is-inhabited : X ≃ X'
  is-inhabited = pr₁ (isContr-iff-is-𝟙 X) p ● ≃-sym (pr₁ (isContr-iff-is-𝟙 X') p')
  is-Prop : isProp (X ≃ X')
  is-Prop = (pr₂ (Prop-iff-Contr-≡ (X ≃ X')) (embedding-pulls-back-Tlevel ⟨-2⟩ (X ≃ X') (X → X') pr₁ (pr₁-is-embedding X X') (→-preserves-Tlevel (S ⟨-2⟩) X X' (cumulativity-of-Tlevels ⟨-2⟩ _ p'))))

Tlevel-Type-if-of-next-Tlevel (S n) (X , p) (X' , p') = ≃-preserves-Tlevel (S n) (X ≃ X') _ (≃-sym (irrelevance-of-Tdata (S n) _ _)) (embedding-pulls-back-Tlevel n (X ≃ X') (X → X') pr₁ (pr₁-is-embedding X X') (→-preserves-Tlevel (S n) X X' p'))


-- Translation to old terminology (isContr, isProp, isSet)

isContr-≃-is-⟨-2⟩-type : (A : 𝓤 ̇) → isContr A ≃ is ⟨-2⟩ type A
isContr-≃-is-⟨-2⟩-type A = idtoeqv _ _ (refl _)

isProp-≃-is-⟨-1⟩-type : (A : 𝓤 ̇) → isProp A ≃ is ⟨-1⟩ type A
isProp-≃-is-⟨-1⟩-type A = biimplication-to-≃ _ _ (isProp-is-Prop _) (Tlevel-is-property ⟨-1⟩ A ) (pr₁ (Prop-iff-Contr-≡ _)) (pr₂ (Prop-iff-Contr-≡ _))

isSet-≃-is-⟨0⟩-type : (A : 𝓤 ̇) → isSet A ≃ is ⟨0⟩ type A
isSet-≃-is-⟨0⟩-type A = biimplication-to-≃ _ _ (isSet-is-Prop _) (Tlevel-is-property ⟨0⟩ _) (λ A-is-Set x y → pr₁ (isProp-≃-is-⟨-1⟩-type _) (A-is-Set x y)) λ A-is-⟨0⟩-type x y → pr₁ (≃-sym (isProp-≃-is-⟨-1⟩-type _)) (A-is-⟨0⟩-type x y)

≃-preserves-Contr : (A : 𝓤 ̇) (B : 𝓥 ̇) → A ≃ B → isContr A → isContr B
≃-preserves-Contr = ≃-preserves-Tlevel ⟨-2⟩ 

retractions-preserve-Props : (A : 𝓤 ̇) (B : 𝓥 ̇) → B ◁ A → isProp A → isProp B
retractions-preserve-Props A B ρ = pr₁ (≃-sym (isProp-≃-is-⟨-1⟩-type B)) ∘ retractions-preserve-Tlevel ⟨-1⟩ B A ρ ∘ pr₁ (isProp-≃-is-⟨-1⟩-type A) 

≃-preserves-Props : (A : 𝓤 ̇) (B : 𝓥 ̇) → A ≃ B → isProp A → isProp B
≃-preserves-Props A B e = pr₁ (≃-sym (isProp-≃-is-⟨-1⟩-type B)) ∘ ≃-preserves-Tlevel ⟨-1⟩ A B e ∘ pr₁ (isProp-≃-is-⟨-1⟩-type A) 

≃-preserves-Set : (A : 𝓤 ̇) (B : 𝓥 ̇) → A ≃ B → isSet A → isSet B
≃-preserves-Set A B e = pr₁ (≃-sym (isSet-≃-is-⟨0⟩-type B)) ∘ ≃-preserves-Tlevel ⟨0⟩ A B e ∘ pr₁ (isSet-≃-is-⟨0⟩-type A)


-- Lemma 3.3.3 continued (logically equivalent propositions are equivalent).

-- (i) Equivalence to a proposition is a proposition

≃-to-Prop-is-Prop : (P : 𝓤 ̇ ) (Q : 𝓥 ̇ ) → isProp Q → isProp (P ≃ Q)
≃-to-Prop-is-Prop P Q Q-is-Prop = pr₁ (≃-sym (isProp-≃-is-⟨-1⟩-type _)) (Σ-preserves-Tlevel _ _ _ (pr₁ (isProp-≃-is-⟨-1⟩-type _) (→-preserves-Props _ _ Q-is-Prop)) (λ f → pr₁ (isProp-≃-is-⟨-1⟩-type _) (ishae-is-Prop f) ))

-- (ii) ≃-sym is its own quasi-inverse

qinv-≃-sym : (A : 𝓤 ̇) (B : 𝓥 ̇) → qinv (≃-sym {𝓤} {𝓥} {A} {B})
qinv-≃-sym A B = ≃-sym , (λ e⁻¹ → Σ-over-predicate _ _ ishae-is-Prop _ _ (refl _)) , (λ e → Σ-over-predicate _ _ ishae-is-Prop _ _ (refl _))

-- (iii) (i) symmetrized

≃-to-Prop-is-Prop' : (P : 𝓤 ̇ ) (Q : 𝓥 ̇ ) → isProp P → isProp (P ≃ Q)
≃-to-Prop-is-Prop' P Q P-is-Prop = ≃-preserves-Props (Q ≃ P) _ (≃-sym , qinv-to-isequiv (qinv-≃-sym _ _)) (≃-to-Prop-is-Prop _ _ P-is-Prop) where

-- (iv) The lemma

biimplication-of-Props-is-≃ : (P : 𝓤 ̇) (Q : 𝓥 ̇) → isProp P → isProp Q → (P → Q) × (Q → P) ≃ (P ≃ Q)
biimplication-of-Props-is-≃ P Q P-is-Prop Q-is-Prop = biimplication-to-≃ _ _ (×-preserves-Props _ _ (→-preserves-Props _ _ Q-is-Prop) (→-preserves-Props _ _ P-is-Prop)) (≃-to-Prop-is-Prop _ _ Q-is-Prop) (Σ-induction (biimplication-to-≃ _ _ P-is-Prop Q-is-Prop)) (≃-to-biimplication _ _)

-- (v) Corollary : retraction of proposition gives equivalence

retraction-of-Prop-to-≃ : {X : 𝓤 ̇} {Y : 𝓥 ̇} → isProp X → Y ◁ X → X ≃ Y
retraction-of-Prop-to-≃ {𝓤} {𝓥} {X} {Y} X-is-Prop (r , s , α) = biimplication-to-≃ _ _ X-is-Prop (retractions-preserve-Props X Y (r , s , α) X-is-Prop) r s 



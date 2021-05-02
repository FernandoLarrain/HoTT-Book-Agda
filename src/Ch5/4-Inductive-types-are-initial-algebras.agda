{-# OPTIONS --without-K --exact-split --safe #-}

open import Ch1.Type-theory
open import Ch2.Homotopy-type-theory
open import Ch3.Sets-and-logic
open import Ch4.Equivalences
open import Ch5.1-Introduction-to-inductive-types
open import Ch5.3-W-types

module Ch5.4-Inductive-types-are-initial-algebras ⦃ fe : FunExt ⦄ where


-- Definition 5.4.1 (ℕ-algebra).

ℕAlg : (𝓤 : Universe) → 𝓤 ⁺ ̇ 
ℕAlg 𝓤 = Σ C ꞉ 𝓤 ̇ , C × (C → C)


-- Definition 5.4.2 (ℕ-homomorphism).

is-ℕAlg-homomorphism : (C : ℕAlg 𝓤) (D : ℕAlg 𝓥) → (pr₁ C → pr₁ D) → 𝓤 ⊔ 𝓥 ̇
is-ℕAlg-homomorphism {𝓤} (C , c₀ , cs) (D , d₀ , ds) h = (h c₀ ≡ d₀) × (h ∘ cs ∼ ds ∘ h)

ℕHom : ℕAlg 𝓤 → ℕAlg 𝓥 → 𝓤 ⊔ 𝓥 ̇
ℕHom C D = Σ h ꞉ (pr₁ C → pr₁ D) , is-ℕAlg-homomorphism C D h

ℕHom-comp : (C : ℕAlg 𝓤) (D : ℕAlg 𝓤) (E : ℕAlg 𝓤) → ℕHom D E → ℕHom C D → ℕHom C E
ℕHom-comp C D E (g , q , β) (f , p , α) = (g ∘ f) , (ap g p ∙ q) , λ x → ap g (α x) ∙ β (f x)

ℕAlg-id : (C : ℕAlg 𝓤) → ℕHom C C
ℕAlg-id (C , c₀ , cs) = id , (refl c₀) , hrefl cs


-- Identity type of ℕ-homomorphisms

module ℕHom-≡ (C : 𝓤 ̇) (D : 𝓤 ̇) (cs : C → C) (ds : D → D) where

  P : (C → D) → 𝓤 ̇
  P h = h ∘ cs ∼ ds ∘ h 

  transport-lemma' : {f g : C → D} (p : f ≡ g) (α : f ∘ cs ∼ ds ∘ f) (c : C) → transport P p α c ≡ happly p (cs c) ⁻¹ ∙ α c ∙ ap ds (happly p c)   
  transport-lemma' (refl _) α c = lu _ ∙ ru _

  transport-lemma : {f g : C → D} (γ : f ∼ g) (α : f ∘ cs ∼ ds ∘ f) (c : C) → transport P (funext γ) α c ≡ γ (cs c) ⁻¹ ∙ α c ∙ ap ds (γ c)   
  transport-lemma γ α c = transport-lemma' (funext γ) α c ∙ ((ap _⁻¹ (happly-β γ (cs c)) ∙ᵣ α c) ✦ ap (ap ds) (happly-β γ c))


-- Isomorphic ℕ-algebras are equal.

_ℕAlg-≅_ : ℕAlg 𝓤 → ℕAlg 𝓤 → 𝓤 ̇
C ℕAlg-≅ D = Σ f ꞉ ℕHom C D , Σ g ꞉ ℕHom D C , (ℕHom-comp D C D f g ≡ ℕAlg-id D) × (ℕHom-comp C D C g f ≡ ℕAlg-id C)

ℕAlg-≅-to-≃ : {C D : ℕAlg 𝓤} → C ℕAlg-≅ D → pr₁ C ≃ pr₁ D
ℕAlg-≅-to-≃ ((f , f-is-hom) , (g , g-is-hom) , p , q) with dpr-≡ p | dpr-≡ q
... | (p' , p-etc) | (q' , q-etc) = f , qinv-to-isequiv (g , (happly p' , happly q'))

ℕAlg-≅-to-≡ : (univ : Univalence) → {C D : ℕAlg 𝓤} → C ℕAlg-≅ D → C ≡ D
ℕAlg-≅-to-≡ {𝓤} univ {C , c₀ , cs} {D , d₀ , ds} ((f , p , α) , (g , q , β) , p' , q') = dpair-≡ (carrier-≡ , (transport-pair id (λ X → X → X) carrier-≡ (c₀ , cs) ∙ pair-≡ (zero-≡ , succ-≡))) where
  open Basic-Univalence univ
  carrier-≃ : C ≃ D
  carrier-≃ = ℕAlg-≅-to-≃ ((f , p , α) , (g , q , β) , p' , q')
  carrier-≡ : C ≡ D
  carrier-≡ = ua carrier-≃
  zero-≡ : coe carrier-≡ c₀ ≡ d₀
  zero-≡ = idtoeqv-β carrier-≃ c₀ ∙ p 
  succ-≡ : transport (λ X → X → X) carrier-≡ cs ≡ ds
  succ-≡ = funext (λ d → transport-fun carrier-≡ cs d ∙ (idtoeqv-β carrier-≃ (cs (coe (carrier-≡ ⁻¹) d)) ∙ (ap (f ∘ cs) (happly (ap coe (type-sym carrier-≃) ∙ funext (idtoeqv-β (≃-sym carrier-≃))) d) ∙ (α (g d) ∙ ap ds (happly (pr₁ (dpr-≡ p')) d)))))


module single-universe where

  -- Definition 5.4.3 (homotopy-initial ℕ-algebra).

  {- Note: We are restricting the definition to a single universe to be able to use univalence in 5.4.4. -}

  isHinit-ℕ : ℕAlg 𝓤 → 𝓤 ⊔ 𝓥 ⁺ ̇
  isHinit-ℕ {𝓤} {𝓥} I = (C : ℕAlg 𝓥) → isContr (ℕHom I C)

  isHinit-ℕ-is-Prop : (I : ℕAlg 𝓤) → isProp (isHinit-ℕ {𝓤} {𝓥} I)
  isHinit-ℕ-is-Prop I = Π-preserves-Props _ (λ C → isContr-is-Prop _)

  Hinit-ℕAlg : (𝓤 𝓥 : Universe) → (𝓤 ⊔ 𝓥) ⁺ ̇
  Hinit-ℕAlg 𝓤 𝓥 = Σ C ꞉ ℕAlg 𝓤 , isHinit-ℕ {𝓤} {𝓥} C


  -- Theorem 5.4.4 (h-inital ℕ-algebras are equal).

  Hinit-ℕAlg-is-Prop : (univ : Univalence) →  isProp (Hinit-ℕAlg 𝓤 𝓤)
  Hinit-ℕAlg-is-Prop {𝓤} univ ((UI , i₀ , is) , i) ((UJ , j₀ , js) , j) =
    let I = (UI , i₀ , is)
        J = (UJ , j₀ , js)
    in Σ-over-predicate isHinit-ℕ-is-Prop (ℕAlg-≅-to-≡ univ (
    pr₁ (i J) ,
    pr₁ (j I) ,
    isContr-to-isProp (j J) _ _ ,
    isContr-to-isProp (i I) _ _
    ))


  -- Theorem 5.4.5 ((ℕ , 0 , succ) is h-initial)

  ℕ-is-h-initial : isHinit-ℕ (ℕ , 0 , succ)
  ℕ-is-h-initial (C , c₀ , cs) = (f , p , α) , contraction where

    -- Center of contraction

    f : ℕ → C
    f zero = c₀
    f (succ n) = cs (f n)
    p : f 0 ≡ c₀
    p = refl _
    α : f ∘ succ ∼ cs ∘ f
    α zero = refl _
    α (succ n) = ap cs (α n)

    -- Contraction

    contraction : Π (λ (h : ℕHom (ℕ , 0 , succ) (C , c₀ , cs)) → (f , p , α) ≡ h)
    contraction (g , q , β) = dpair-≡ (fun-≡ , (transport-pair (λ h → h 0 ≡ c₀) (λ h → h ∘ succ ∼ cs ∘ h) fun-≡ (p , α) ∙ pair-≡ (path-≡ , htpy-≡) )) where

      fun-∼ : f ∼ g
      fun-∼ = ℕ-uniqueness-pple' (λ - → C) c₀ (λ n → cs) f g p α q β
      fun-≡ : f ≡ g 
      fun-≡ = ℕ-uniqueness-pple (λ - → C) c₀ (λ n → cs) f g p α q β

      path-≡ : transport (λ h → h 0 ≡ c₀) fun-≡ p ≡ q
      path-≡ = transport-funval-≡' 0 c₀ fun-≡ p ∙ (ap (λ - → - ⁻¹ ∙ p) (happly-β fun-∼ 0) ∙ ru _ ⁻¹ ∙ distr _ _ ∙ ru _ ⁻¹ ∙ ⁻¹-invol q)

      htpy-∼ : transport (λ h → h ∘ succ ∼ cs ∘ h) fun-≡ α ∼ β

      -- Base case

      htpy-∼ zero =
        transport (λ h → h ∘ succ ∼ cs ∘ h) fun-≡ α 0
          ≡⟨ ℕHom-≡.transport-lemma ℕ C succ cs fun-∼ α 0 ⟩
        (refl (cs c₀) ∙ ap cs (refl c₀ ∙ q ⁻¹) ∙ β 0 ⁻¹) ⁻¹ ∙ refl (cs c₀) ∙ ap cs (refl c₀ ∙ q ⁻¹)
          ≡⟨ aux-path  ⟩
        (β 0) ∎

        where

        aux-path : (refl (cs c₀) ∙ ap cs (refl c₀ ∙ q ⁻¹) ∙ β 0 ⁻¹) ⁻¹ ∙ refl (cs c₀) ∙ ap cs (refl c₀ ∙ q ⁻¹) ≡ β 0
        aux-path rewrite  
          lu (q ⁻¹) ⁻¹ |
          lu (ap cs (q ⁻¹)) ⁻¹ |
          distr (ap cs (q ⁻¹)) (β 0 ⁻¹) |
          ru ((β 0 ⁻¹) ⁻¹ ∙ ap cs (q ⁻¹) ⁻¹) ⁻¹ |
          ∙-assoc ((β 0 ⁻¹) ⁻¹) (ap cs (q ⁻¹) ⁻¹) (ap cs (q ⁻¹)) ⁻¹ |
          linv (ap cs (q ⁻¹)) |
          ru ((β 0 ⁻¹) ⁻¹) ⁻¹ |
          ⁻¹-invol (β 0)
          = refl _

      -- Inductive step

      htpy-∼ (succ n) =
        transport (λ h → h ∘ succ ∼ cs ∘ h) fun-≡ α (succ n)
          ≡⟨ ℕHom-≡.transport-lemma ℕ C succ cs fun-∼ α (succ n) ⟩
        fun-∼ (succ (succ n)) ⁻¹ ∙ ap cs (α n) ∙ ap cs (fun-∼ (succ n))
          ≡⟨ refl _ ⟩
        (α (succ n) ∙ ap cs (fun-∼ (succ n)) ∙ β (succ n) ⁻¹) ⁻¹ ∙ α (succ n) ∙ ap cs (fun-∼ (succ n))
          ≡⟨ aux-path ⟩
        β (succ n) ∎

        where

        p₁ =  α (succ n)
        p₂ = ap cs (fun-∼ (succ n))
        p₃ = β (succ n)
        aux-path : (p₁ ∙ p₂ ∙ p₃ ⁻¹) ⁻¹ ∙ p₁ ∙ p₂ ≡ p₃
        aux-path rewrite
          distr (p₁ ∙ p₂) (p₃ ⁻¹) |
          ∙-assoc ((p₃ ⁻¹) ⁻¹) ((p₁ ∙ p₂) ⁻¹) p₁ ⁻¹ |
          distr p₁ p₂ |
          ∙-assoc (p₂ ⁻¹) (p₁ ⁻¹) p₁ ⁻¹ |
          linv p₁ |
          ru (p₂ ⁻¹) ⁻¹ |
          ∙-assoc ((p₃ ⁻¹) ⁻¹) (p₂ ⁻¹) p₂ ⁻¹ |
          linv p₂ |
          ru ((p₃ ⁻¹) ⁻¹) ⁻¹ |
          ⁻¹-invol p₃        
          = refl _

      htpy-≡ : transport (λ h → h ∘ succ ∼ cs ∘ h) fun-≡ α ≡ β
      htpy-≡ = funext htpy-∼


{- The book does not treat the case of W-types in detail. The following follows "Homotopy-initial algebras in type theory" (Awodey, Gambino & Sojakova, 2016). -}

module W-types {𝓤 : Universe} (A : 𝓤 ̇) (B : A → 𝓤 ̇) where

  -- 1. P-algebras and their morphisms

  --Definition (Polynomial functor associated to A and B).

  P₀ : 𝓤 ̇ → 𝓤 ̇
  P₀ C = Σ x ꞉ A , (B x → C)

  P₁ : {C D : 𝓤 ̇} → (C → D) → P₀ C → P₀ D
  P₁ f (x , u) = x , (f ∘ u)

  P₂ : {C D : 𝓤 ̇} {f g : C → D} → (f ∼ g) → P₁ f ∼ P₁ g
  P₂ α (x , u) = dpair-≡ ((refl _) , funext (α ∘ u))

  -- Functoriality of P (we have judgemental η-rule for dependent pairs).

  φ-∘ : {C D E : 𝓤 ̇} (f : C → D) (g : D → E) → P₁ (g ∘ f) ≡ P₁ g ∘ P₁ f
  φ-∘ f g = refl _

  φ-𝑖𝑑 : (C : 𝓤 ̇) → P₁ (𝑖𝑑 C) ≡ 𝑖𝑑 (P₀ C)
  φ-𝑖𝑑 C = refl _

  -- Definition 4.2 (P-algebra).

  PAlg : 𝓤 ⁺ ̇
  PAlg = Σ C ꞉ (𝓤 ̇) , (P₀ C → C)

  -- Definition (is algebra homomorphism).

  isalghom : (C D : PAlg) → (pr₁ C → pr₁ D) → 𝓤 ̇
  isalghom (C , sc) (D , sd) f = f ∘ sc ∼ sd ∘ P₁ f

  --  Definition 4.3 (P-algebra morphism).

  PHom : PAlg → PAlg → 𝓤 ̇
  PHom (C , sc) (D , sd) = Σ f ꞉ (C → D) , isalghom (C , sc) (D , sd) f

  -- Definition (Composition of P-algebra morphisms).

  Pcomp : (C D E : PAlg) → PHom D E → PHom C D → PHom C E
  Pcomp (C , sc) (D , sd) (E , se) (g , g') (f , f') = (g ∘ f) , λ w → ap g (f' w) ∙ g' (P₁ f w)

  -- Definition (Identity morphism).

  Pid : (C : PAlg) → PHom C C
  Pid (C , sc) = id , (hrefl _)

  -- Definition 4.4 (P-algebra homotopy).

  PHot : (C D : PAlg) → PHom C D → PHom C D → 𝓤 ̇
  PHot (C , sc) (D , sd) (f , f') (g , g') = Σ α ꞉ (f ∼ g) , ((w : P₀ C) → f' w ∙ ap sd (P₂ α w) ≡ α (sc w) ∙ g' w)

  -- -- Lemma 4.5: Characterization of the identity type of morphisms

  -- -- PHom-≡-elim : (C D : PAlg) (f g : PHom C D) → f ≡ g → PHot C D f g
  -- -- PHom-≡-elim (C , sc) (D , sd) (f , f') (.f , .f') (refl .(f , f')) = (hrefl _) , (Σ-induction λ x u → (f' (x , u) ∙ₗ {!!}) ∙ ru _ ⁻¹ ∙ lu _)

  -- PHom-≡-≃ : (C D : PAlg) (f g : PHom C D) → (f ≡ g) ≃ PHot C D f g
  -- PHom-≡-≃ (C , sc) (D , sd) (f , f') (g , g') =
  --   ((f , f') ≡ (g , g'))
  --     ≃⟨ Σ-≡-≃ ⟩
  --   (Σ p ꞉ (f ≡ g) , (transport (isalghom (C , sc) (D , sd)) p f' ≡ g'))
  --     ≃⟨ Σ-preserves-≃ _ _ (happly , happly-is-equiv) (λ p → (happly , happly-is-equiv) ● (≃-sym ((transport (λ - → transport (isalghom (C , sc) (D , sd)) - f' ∼ g') (happly-η p)) , (qinv-to-isequiv (qinv-transport _ (happly-η p)))))) ⟩
  --   (Σ α ꞉ (f ∼ g) , (transport (isalghom (C , sc) (D , sd)) (funext α) f' ∼ g'))
  --     ≃⟨ Σ-preserves-family-≃ (λ α → {!!}) ⟩
  --   (Σ α ꞉ (f ∼ g) , ((w : P₀ C) → f' w ∙ ap sd (P₂ α w) ≡ α (sc w) ∙ g' w)) ■ 
  --   where
  --   transport-lemma : (p : f ≡ g) →  (transport (isalghom (C , sc) (D , sd)) p f' ∼ g') ≃ ((w : P₀ C) → f' w ∙ ap sd (P₂ (happly p) w) ≡ happly p (sc w) ∙ g' w)
  --   transport-lemma (refl _) = (λ α' → Σ-induction λ x u → (α' (x , u) ✦ ap (ap sd) (transport (λ - → dpair-≡ (refl _ , -) ≡ refl _) (fun-refl _) (refl _))) ∙ ru _ ⁻¹ ∙ lu _ ) , qinv-to-isequiv ((λ β' → Σ-induction λ x u → {!β' (x , u)!}) , {!!} , {!!})
    
  --   aux-≃ : (α : f ∼ g) →  (transport (isalghom (C , sc) (D , sd)) (funext α) f' ∼ g') ≃ ((w : P₀ C) → f' w ∙ ap sd (P₂ α w) ≡ α (sc w) ∙ g' w)
  --   aux-≃ α = {!!}
  

    

  
  

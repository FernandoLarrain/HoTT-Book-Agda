{-# OPTIONS --without-K --exact-split --safe #-}

open import Ch1.Type-theory
open import Ch2.Homotopy-type-theory
open import Ch3.Sets-and-logic
open import Ch4.Equivalences

module Ch5.8-Id-types-and-id-systems where


-- module single-universe where

--   -- Definition 5.8.1 (Pointed predicate, pointed family of maps, based identity system).

--   pted-pred : 𝓤 ⊙ → 𝓤 ⁺ ̇
--   pted-pred {𝓤} (A , a₀) = Σ R ꞉ (A → 𝓤 ̇) , R a₀

--   ppmap : (A : 𝓤 ⊙) → pted-pred A → pted-pred A → 𝓤 ̇
--   ppmap (A , a₀) (R , r₀) (S , s₀) = Σ g ꞉ Π (λ a → R a → S a) , g a₀ r₀ ≡ s₀ 

--   is-based-id-system : {A : 𝓤 ⊙} → pted-pred A  → 𝓤 ⁺ ̇
--   is-based-id-system {𝓤} {A , a₀} (R , r₀) = (D : (a : A) → R a → 𝓤 ̇) (d : D a₀ r₀) → Σ f ꞉ ((a : A) (r : R a) → D a r) , f a₀ r₀ ≡ d


--   -- Identity type of pointed families of maps

--   ppmap-≡ : ⦃ fe : FunExt ⦄ (A : 𝓤 ⊙) (R : pted-pred A) (S : pted-pred A) (g h : ppmap A R S) → (g ≡ h) ≃ (Σ α ꞉ ((a : pr₁ A) (r : pr₁ R a) → pr₁ g a r ≡ pr₁ h a r) , (α (pr₂ A) (pr₂ R) ⁻¹ ∙ pr₂ g ≡ pr₂ h))
--   ppmap-≡ (A , a₀) (R , r₀) (S , s₀) (g , gr) (h , hr) = Σ-≡-equiv ● Σ-preserves-≃ _ _ ((happly , happly-is-equiv) ● Π-preserves-family-≃ (λ a → happly , happly-is-equiv)) λ p → (path p gr ⁻¹ ∙_ ) , (qinv-to-isequiv (qinv-pre-∙ hr (path p gr ⁻¹))) where
--     path : {g h : Π λ a → R a → S a} (p : g ≡ h) (gr : g a₀ r₀ ≡ s₀) → transport (λ - → (- a₀ r₀) ≡ s₀) p gr ≡ happly (happly p a₀) r₀ ⁻¹ ∙ gr  
--     path (refl _) gr = lu _


--   -- Composition of pointed families of maps

--   ppmap-comp : (A : 𝓤 ⊙) (R S T : pted-pred A) → ppmap A R S → ppmap A S T → ppmap A R T
--   ppmap-comp (A , a₀) (R , r₀) (S , s₀) (T , t₀) (f , fr) (g , gr) = (λ a → g a ∘ f a) , (ap (g a₀) fr ∙ gr)


--   -- Identity pointed familiy of maps

--   ppmap-id : (A : 𝓤 ⊙) (R : pted-pred A) → ppmap A R R
--   ppmap-id (A , a₀) (R , r₀) = (λ a → id) , (refl r₀)
 

--   -- Theorem 5.8.2 (Fundamental theorem of based identity types).

--   module thm-5-8-2 ⦃ fe : FunExt ⦄ (A' : 𝓤 ⊙) (R' : pted-pred A') where

--   -- Unfold the pointed type and predicate

--     A = pr₁ A'
--     a₀ = pr₂ A'
--     R = pr₁ R'
--     r₀ = pr₂ R'

--     -- TFAE

--     i = is-based-id-system R'
--     ii = (S' : pted-pred A') → isContr (ppmap A' R' S')
--     iii = (a : A) → isequiv (λ (- : a₀ ≡ a) → transport R - r₀)
--     iv = isContr (Σ R)

--     -- The statements are propositions (the proof of i-is-Prop is omitted).

--     ii-is-Prop : isProp ii
--     ii-is-Prop = Π-preserves-Props _ (λ S' → isContr-is-Prop _)

--     iii-is-Prop : isProp iii
--     iii-is-Prop = Π-preserves-Props _ (λ a → ishae-is-Prop _)

--     iv-is-Prop : isProp iv
--     iv-is-Prop = isContr-is-Prop _

--     -- Proof of the logical equivalences

--     i-to-ii : i → ii
--     i-to-ii R'-is-based-id-system (S , s₀) = pr₂ isContr-iff-is-inhabited-Prop (inhabited , is-Prop) where
--       inhabited : ppmap A' R' (S , s₀)
--       inhabited = R'-is-based-id-system (λ a r → S a) s₀
--       is-Prop : isProp (ppmap A' R' (S , s₀))
--       is-Prop (f , fr) (g , gr) =
--         let R'-ind = R'-is-based-id-system (λ a r → f a r ≡ g a r) (fr ∙ gr ⁻¹)
--         in inv (ppmap-≡ A' R' (S , s₀) (f , fr) (g , gr)) (
--           pr₁ R'-ind ,
--           (((ap _⁻¹ (pr₂ (R'-ind)) ∙ distr _ _) ∙ᵣ fr) ∙ (∙-assoc _ _ _ ⁻¹ ∙ (ap (λ - → (gr ⁻¹) ⁻¹ ∙ -) (linv _) ∙ ru _ ⁻¹ ∙ ⁻¹-invol _)))
--           )

--     ii-to-iii : ii → iii
--     ii-to-iii R'-is-initial = λ a → qinv-to-isequiv (pr₁ inv-ppmap a , α' a , β' a)
--       where

--       -- Identity is a pointed predicate

--       S : A → 𝓤 ̇
--       S a = a₀ ≡ a
--       s₀ : S a₀
--       s₀ = refl a₀
--       S' : pted-pred A'
--       S' = (S , s₀)

--       -- Inverse pointed family of maps

--       Contr₁ : isContr (ppmap A' R' S')
--       Contr₁ = R'-is-initial S'
--       inv-ppmap : ppmap A' R' S' 
--       inv-ppmap = pr₁ Contr₁

--       -- Right-invertibility

--       Contr₂ : isContr (ppmap A' R' R')
--       Contr₂ = R'-is-initial R'
--       α : ppmap-comp A' R' S' R' inv-ppmap ((λ a p → transport R p r₀) , refl r₀) ≡ ppmap-id A' R'
--       α = pr₂ (pr₁ isContr-iff-is-inhabited-Prop Contr₂) _ _
--       α' : (a : A) (r : R a) → transport R (pr₁ inv-ppmap a r) r₀ ≡ r
--       α' = pr₁ (pr₁ (ppmap-≡ A' R' R' (ppmap-comp A' R' S' R' inv-ppmap ((λ a p → transport R p r₀) , refl r₀)) (ppmap-id A' R')) α)

--       -- Left-invertibility

--       Contr₃ : isContr (ppmap A' S' S')
--       Contr₃ = ppmap-id A' S' , Σ-induction (λ f fr → inv (ppmap-≡ A' S' S' (ppmap-id A' S') (f , fr)) ((ℍ a₀ (λ a p → pr₁ (ppmap-id A' S') a p ≡ f a p) (fr ⁻¹)) , (ru _ ⁻¹ ∙ ⁻¹-invol _)))
--       β : ppmap-comp A' S' R' S' ((λ a p → transport R p r₀) , refl r₀) inv-ppmap ≡ ppmap-id A' S'
--       β = pr₂ Contr₃ _ ⁻¹
--       β' : (a : A) (p : S a) → pr₁ inv-ppmap a (transport R p r₀) ≡ p
--       β' = pr₁ (pr₁ (ppmap-≡ A' S' S' (ppmap-comp A' S' R' S' ((λ a p → transport R p r₀) , refl r₀) inv-ppmap) (ppmap-id A' S')) β)


--     iii-to-iv : iii → iv
--     iii-to-iv transport-is-equiv = ≃-preserves-Contr (Σ-preserves-family-≃ (λ a → (λ (p : a₀ ≡ a) → transport R p r₀) , transport-is-equiv a)) (free-right-endpt-is-Contr A a₀)


--     iv-to-i : iv → i
--     iv-to-i ΣR-is-Contr D d = (curry (λ u → transport (Σ-induction D) (p u) d)) , (ap (λ - → transport (Σ-induction D) - d) q) where
--       p : (u : Σ R) → (a₀ , r₀) ≡ u
--       p = pr₂ (pr₁ isContr-iff-is-inhabited-Prop ΣR-is-Contr) (a₀ , r₀)
--       q : p (a₀ , r₀) ≡ refl (a₀ , r₀)
--       q = pr₂ (pr₁ isContr-iff-is-inhabited-Prop (pr₁ (Prop-iff-Contr-≡ (Σ R)) (pr₂ (pr₁ isContr-iff-is-inhabited-Prop ΣR-is-Contr)) (a₀ , r₀) (a₀ , r₀))) _ _ 


module multiple-universes where

  -- Definition 5.8.1 (Pointed predicate, pointed family of maps (pointed-predicate map) and based identity system).

  pted-pred : 𝓤 ⊙ → (𝓥 : Universe) → 𝓤 ⊔ 𝓥 ⁺ ̇
  pted-pred {𝓤} (A , a₀) 𝓥 = Σ R ꞉ (A → 𝓥 ̇) , R a₀

  ppmap : {A : 𝓤 ⊙} → pted-pred A 𝓥 → pted-pred A 𝓦 → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ̇
  ppmap {𝓤} {𝓥} {𝓦} {A , a₀} (R , r₀) (S , s₀) = Σ g ꞉ Π (λ a → R a → S a) , g a₀ r₀ ≡ s₀ 

  is-based-id-system : {A : 𝓤 ⊙} → pted-pred A 𝓥 → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ⁺ ̇ 
  is-based-id-system {𝓤} {𝓥} {𝓦} {A , a₀} (R , r₀) = (D : (a : A) → R a → 𝓦 ̇) (d : D a₀ r₀) → Σ f ꞉ ((a : A) (r : R a) → D a r) , f a₀ r₀ ≡ d


  -- Based identity is a pointed predicate

  Id⊙ : (A : 𝓤 ⊙) → pted-pred A 𝓤
  Id⊙ (A , a₀) = (Id A a₀) , (refl a₀)
  

  -- Composition of pointed families of maps

  _∘pp_ : {A : 𝓤 ⊙} {R : pted-pred A 𝓥} {S : pted-pred A 𝓦} {T : pted-pred A 𝓣} → ppmap S T → ppmap R S → ppmap R T
  _∘pp_ {𝓤} {𝓥} {𝓦} {𝓣} {A , a₀} {R , r₀} {S , s₀} {T , t₀} (g , gr) (f , fr) = (λ a → g a ∘ f a) , (ap (g a₀) fr ∙ gr)


  -- Pointed family of identity maps

  ppmap-id : {A : 𝓤 ⊙} (R : pted-pred A 𝓥) → ppmap R R
  ppmap-id (R , r₀) = (λ a → id) , (refl r₀)


  -- Identity type of pointed families of maps

  ppmap-≡ : ⦃ fe : FunExt ⦄ (A : 𝓤 ⊙) (R : pted-pred A 𝓥) (S : pted-pred A 𝓦) (g h : ppmap R S) → (g ≡ h) ≃ (Σ α ꞉ ((a : pr₁ A) (r : pr₁ R a) → pr₁ g a r ≡ pr₁ h a r) , (α (pr₂ A) (pr₂ R) ⁻¹ ∙ pr₂ g ≡ pr₂ h))
  
  ppmap-≡ (A , a₀) (R , r₀) (S , s₀) (g , gr) (h , hr) =
    Σ-≡-equiv ●
    Σ-preserves-≃ _ _
      ((happly , happly-is-equiv) ● Π-preserves-family-≃ (λ a → happly , happly-is-equiv))
      λ p → (transport-lemma p gr ⁻¹ ∙_ ) , (qinv-to-isequiv (qinv-pre-∙ hr _))

    where
    
    transport-lemma : {g h : Π λ a → R a → S a} (p : g ≡ h) (gr : g a₀ r₀ ≡ s₀) → transport (λ - → (- a₀ r₀) ≡ s₀) p gr ≡ happly (happly p a₀) r₀ ⁻¹ ∙ gr  
    transport-lemma (refl _) gr = lu _


  -- Example

  ppendomap-Id⊙-is-Contr : ⦃ fe : FunExt ⦄ (A' : 𝓤 ⊙) → isContr (ppmap (Id⊙ A') (Id⊙ A'))
  ppendomap-Id⊙-is-Contr (A , a₀) = let A' = (A , a₀) in
    ppmap-id (Id⊙ A') ,
    Σ-induction (λ f fr → inv (ppmap-≡ A' (Id⊙ A') (Id⊙ A') (ppmap-id (Id⊙ A')) (f , fr)) ((ℍ a₀ (λ a p → pr₁ (ppmap-id (Id⊙ A')) a p ≡ f a p) (fr ⁻¹)) , (ru _ ⁻¹ ∙ ⁻¹-invol _)))


  -- Theorem 5.8.2 (Fundamental theorem of based identity types).

  module thm-5-8-2 ⦃ fe : FunExt ⦄ (A' : 𝓤 ⊙) (R' : pted-pred A' 𝓥) where

    -- I. Lift bureaucracy

    -- Unfold the pointed type and predicate

    A = pr₁ A'
    a₀ = pr₂ A'
    
    R = pr₁ R'
    r₀ = pr₂ R'

    -- Lift R'

    ↑R : A → 𝓤 ⊔ 𝓥 ̇
    ↑R = Lift 𝓤 ∘ R
    ↑r₀ : ↑R a₀
    ↑r₀ = lift r₀
    ↑R' : pted-pred A' (𝓤 ⊔ 𝓥)
    ↑R' = (↑R , ↑r₀)

    -- ppmap from ↑R' to R'

    ↑R'-to-R' : ppmap ↑R' R'
    ↑R'-to-R' = (λ a → lower) , refl _

    -- Lift Id

    ↑Id : A → 𝓤 ⊔ 𝓥 ̇
    ↑Id a = Lift 𝓥 (a₀ ≡ a)
    ↑Id⊙ : pted-pred A' (𝓤 ⊔ 𝓥)
    ↑Id⊙ = (↑Id , lift (refl a₀))

    -- ppmap from ↑Id⊙ to Id⊙ 

    ↑Id⊙-to-Id⊙ : ppmap ↑Id⊙ (Id⊙ A')
    ↑Id⊙-to-Id⊙ = (λ a → lower) , refl _


    -- II. The statements

    -- Statements (the first two are actually "statement schemas" indexed by 𝓦).

    i : 𝓤 ⊔ 𝓥 ⊔ 𝓦 ⁺ ̇ 
    i {𝓦} = is-based-id-system {𝓤} {𝓥} {𝓦} R'
    
    ii : 𝓤 ⊔ 𝓥 ⊔ 𝓦 ⁺ ̇
    ii {𝓦} = (S' : pted-pred A' 𝓦) → isContr (ppmap R' S')
    
    iii = (a : A) → isequiv (λ (- : a₀ ≡ a) → transport R - r₀)
    
    iv = isContr (Σ R)
    

    -- The statements are propositions (the proof of i-is-Prop is omitted).

    ii-is-Prop : isProp (ii {𝓦})
    ii-is-Prop = Π-preserves-Props _ (λ S' → isContr-is-Prop _)

    iii-is-Prop : isProp iii
    iii-is-Prop = Π-preserves-Props _ (λ a → ishae-is-Prop _)

    iv-is-Prop : isProp iv
    iv-is-Prop = isContr-is-Prop _
    

    -- III. Proof of the logical equivalences


    -- III.1. Based identity systems are initial

    i-to-ii : i {𝓦} → ii {𝓦}
    i-to-ii R'-is-based-id-system (S , s₀) = pr₂ isContr-iff-is-inhabited-Prop (inhabited , is-Prop) where
      inhabited : ppmap R' (S , s₀)
      inhabited = R'-is-based-id-system (λ a r → S a) s₀
      is-Prop : isProp (ppmap R' (S , s₀))
      is-Prop (f , fr) (g , gr) =
        let R'-ind = R'-is-based-id-system (λ a r → f a r ≡ g a r) (fr ∙ gr ⁻¹)
        in inv (ppmap-≡ A' R' (S , s₀) (f , fr) (g , gr)) (
          pr₁ R'-ind ,
          (((ap _⁻¹ (pr₂ (R'-ind)) ∙ distr _ _) ∙ᵣ fr) ∙ (∙-assoc _ _ _ ⁻¹ ∙ (ap (λ - → (gr ⁻¹) ⁻¹ ∙ -) (linv _) ∙ ru _ ⁻¹ ∙ ⁻¹-invol _)))
          )
          

    -- III.2. Initiality in 𝓤 ⊔ 𝓥 ⊔ 𝓦 implies initiality in 𝓤 ⊔ 𝓥 

    ii-to-ii : ii {𝓤 ⊔ 𝓥 ⊔ 𝓦} → ii {𝓤 ⊔ 𝓥}
    ii-to-ii {𝓦} R'-is-initial (S , s₀) = ≃-preserves-Contr aux-equiv (R'-is-initial ↑S')
    
      where

      S' : pted-pred A' (𝓤 ⊔ 𝓥)
      S' = (S , s₀)

      -- Lifting (S , s₀)
      
      ↑S : A → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ̇
      ↑S = Lift 𝓦 ∘ S
      ↑s₀ : ↑S a₀
      ↑s₀ = lift s₀
      ↑S' : pted-pred A' (𝓤 ⊔ 𝓥 ⊔ 𝓦)
      ↑S' = (↑S , ↑s₀)

      -- ppmap from ↑S' to S

      ↑S'-to-S' : ppmap ↑S' S'
      ↑S'-to-S' = (λ a → lower) , refl _

      -- Equivalence of ppmap spaces

      aux-equiv : ppmap R' ↑S' ≃ ppmap R' S'
      aux-equiv = Σ-preserves-≃ _ _
        (Π-preserves-family-≃ (λ a → →-preserves-codom-≃ _ Lift-≃))
        λ g → ap lower , ap-lower-is-equiv


    -- III.3. Initiality in 𝓤 ⊔ 𝓥 implies transport R - r₀ is a fiberwise equivalence

    ii-to-iii : ii {𝓤 ⊔ 𝓥} → iii
    ii-to-iii R'-is-initial = λ a → qinv-to-isequiv (pr₁ inv-ppmap a , α' a , β' a)
 
      where

      -- Inverse pointed family of maps

      inv-ppmap : ppmap R' (Id⊙ A') 
      inv-ppmap = ↑Id⊙-to-Id⊙ ∘pp (pr₁ (R'-is-initial ↑Id⊙))

      -- Right-invertibility

      aux-equiv : ppmap R' ↑R' ≃ ppmap R' R'
      aux-equiv = Σ-preserves-≃ _ _ (Π-preserves-family-≃ (λ a → →-preserves-codom-≃ _ Lift-≃)) (λ g → ap lower , ap-lower-is-equiv)
      
      ppmap-is-Contr : isContr (ppmap R' R')
      ppmap-is-Contr = ≃-preserves-Contr aux-equiv (R'-is-initial ↑R')
      
      α : ((λ a p → transport R p r₀) , refl r₀) ∘pp inv-ppmap ≡ ppmap-id R'
      α = pr₂ (pr₁ isContr-iff-is-inhabited-Prop ppmap-is-Contr) _ _
      α' : (a : A) (r : R a) → transport R (pr₁ inv-ppmap a r) r₀ ≡ r
      α' = pr₁ (pr₁ (ppmap-≡ A' R' R' (((λ a p → transport R p r₀) , refl r₀) ∘pp inv-ppmap) (ppmap-id R')) α)

      -- Left-invertibility

      β : inv-ppmap ∘pp ((λ a p → transport R p r₀) , refl r₀) ≡ ppmap-id (Id⊙ A')
      β = pr₂ (ppendomap-Id⊙-is-Contr A') _ ⁻¹
      β' : (a : A) (p : a₀ ≡ a) → pr₁ inv-ppmap a (transport R p r₀) ≡ p
      β' = pr₁ (pr₁ (ppmap-≡ A' (Id⊙ A') (Id⊙ A') (inv-ppmap ∘pp ((λ a p → transport R p r₀) , refl r₀)) (ppmap-id (Id⊙ A'))) β)


    -- III.4. If transport R - r₀ is a fiberwise equivalence, Σ R is contractible    

    iii-to-iv : iii → iv
    iii-to-iv transport-is-equiv = ≃-preserves-Contr (Σ-preserves-family-≃ (λ a → (λ (p : a₀ ≡ a) → transport R p r₀) , transport-is-equiv a)) (free-right-endpt-is-Contr A a₀)

    --III.5. If Σ R is contractible, R' is a based-identity system
    
    iv-to-i : iv → i {𝓦}
    iv-to-i ΣR-is-Contr D d = (curry (λ u → transport (Σ-induction D) (p u) d)) , (ap (λ - → transport (Σ-induction D) - d) q) where
      p : (u : Σ R) → (a₀ , r₀) ≡ u
      p = pr₂ (pr₁ isContr-iff-is-inhabited-Prop ΣR-is-Contr) (a₀ , r₀)
      q : p (a₀ , r₀) ≡ refl (a₀ , r₀)
      q = pr₂ (pr₁ isContr-iff-is-inhabited-Prop (pr₁ (Prop-iff-Contr-≡ (Σ R)) (pr₂ (pr₁ isContr-iff-is-inhabited-Prop ΣR-is-Contr)) (a₀ , r₀) (a₀ , r₀))) _ _ 


    -- III.6. Other implications

    ii-to-i : ii {𝓤 ⊔ 𝓥} → i {𝓦}
    ii-to-i = iv-to-i ∘ iii-to-iv ∘ ii-to-iii

    iii-to-i : iii → i {𝓦}
    iii-to-i = iv-to-i ∘ iii-to-iv


  -- Definition 5.8.3 (Identity system).

  is-id-system : {A : 𝓤 ̇} → (Σ R ꞉ (A → A → 𝓥 ̇) , ((a : A) → R a a)) → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ⁺ ̇
  is-id-system {𝓤} {𝓥} {𝓦} {A} (R , r₀) = (D : (a b : A) → R a b → 𝓦 ̇) (d : (a : A) → D a a (r₀ a)) → Σ f ꞉ ((a b : A) (r : R a b) → D a b r) , ((a : A) → f a a (r₀ a) ≡ d a)

  refl-rel : 𝓤 ̇ → (𝓥 : Universe) → 𝓤 ⊔ 𝓥 ⁺ ̇
  refl-rel {𝓤} A 𝓥 = Σ R ꞉ (A → A → 𝓥 ̇) , ((a : A) → R a a)

  rrmap : {A : 𝓤 ̇} → refl-rel A 𝓥 → refl-rel A 𝓦 → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ̇
  rrmap {𝓤} {𝓥} {𝓦} {A} (R , r₀) (S , s₀) = Σ g ꞉ ((a b : A) → R a b → S a b) , ((a : A) → g a a (r₀ a) ≡ s₀ a)


  -- Composition of reflexive relation maps

  _∘rr_ : {A : 𝓤 ̇} {R : refl-rel A 𝓥} {S : refl-rel A 𝓦} {T : refl-rel A 𝓣} → rrmap S T → rrmap R S → rrmap R T
  _∘rr_ {𝓤} {𝓥} {𝓦} {𝓣} {A} {R} {S} {T} (g , gr) (f , fr) = (λ a b r → g a b (f a b r)) , (λ a → ap (g a a) (fr a) ∙ gr a)


  -- Identity rrmap

  rrmap-id : {A : 𝓤 ̇} (R : refl-rel A 𝓥) → rrmap R R
  rrmap-id (R , r₀) = (λ a b → id) , (hrefl _)


  -- Relationship between ppmaps and rrmaps
  
  ppmap-≃-rrmap : ⦃ fe : FunExt ⦄ {A : 𝓤 ̇} (R : refl-rel A 𝓥) (S : refl-rel A 𝓦) → ((a₀ : A) → ppmap (pr₁ R a₀ , pr₂ R a₀) (pr₁ S a₀ , pr₂ S a₀)) ≃ (rrmap R S)
  ppmap-≃-rrmap {𝓤} {𝓥} {𝓦} {A} (R , r₀) (S , s₀) = _ , (dep-Σ-UMP A (λ a → (b : A) → R a b → S a b) (λ a ga → ga a (r₀ a) ≡ (s₀ a)))


  -- Identity type of rrmap

  rrmap-≡ : ⦃ fe : FunExt ⦄ (A : 𝓤 ̇) (R : refl-rel A 𝓥) (S : refl-rel A 𝓦) (g h : rrmap R S) → (g ≡ h) ≃ (Σ α ꞉ ((a b : A) (r : pr₁ R a b) → pr₁ g a b r ≡ pr₁ h a b r) , ((a : A) → α a a (pr₂ R a) ⁻¹ ∙ pr₂ g a ≡ pr₂ h a))
  rrmap-≡ A (R , r₀) (S , s₀) (g , gr) (h , hr) =
    Σ-≡-equiv ●
    Σ-preserves-≃ _ _
      ((happly , happly-is-equiv) ● Π-preserves-family-≃ (λ a → (happly , happly-is-equiv) ● Π-preserves-family-≃ (λ b → happly , happly-is-equiv)))
      λ p → (happly , happly-is-equiv) ● Π-preserves-family-≃ (λ a → (transport-lemma p gr a ⁻¹ ∙_) , (qinv-to-isequiv (qinv-pre-∙ (hr a) _)))

    where

    transport-lemma : {g h : (a b : A) → R a b → S a b} (p : g ≡ h) (gr : (a : A) → g a a (r₀ a) ≡ s₀ a) → transport (λ - → (a : A) → - a a (r₀ a) ≡ s₀ a) p gr ∼ λ a → happly (happly (happly p a) a) (r₀ a) ⁻¹ ∙ gr a 
    transport-lemma (refl _) gr a = lu _


  -- Example
  
  rrendomap-Id-is-Contr : ⦃ fe : FunExt ⦄ (A : 𝓤 ̇) → isContr (rrmap (Id A , refl) (Id A , refl))
  rrendomap-Id-is-Contr A =
    (rrmap-id (Id A , refl)) ,
    (Σ-induction (λ f fr → inv (rrmap-≡ A (Id A , refl) (Id A , refl) (rrmap-id (Id A , refl)) (f , fr)) (
      𝕁 A (λ a b p → pr₁ (rrmap-id (Id A , refl)) a b p ≡ f a b p) (hsym fr) ,
      λ a → ru _ ⁻¹ ∙ ⁻¹-invol _
      )))
    

  -- Theorem 5.8.4. (Fundamental theorem of identity types).

  module thm-5-8-4 ⦃ fe : FunExt ⦄ (A : 𝓤 ̇) (R' : refl-rel A 𝓥) where

    -- I. Lift bureaucracy

    -- Unfold R'

    R = pr₁ R'
    r₀ = pr₂ R'

    -- Lift R'

    ↑R : A → A → 𝓤 ⊔ 𝓥 ̇
    ↑R a b = Lift 𝓤 (R a b)
    ↑r₀ : (a : A) → ↑R a a
    ↑r₀ a = lift (r₀ a)
    ↑R' : refl-rel A (𝓤 ⊔ 𝓥)
    ↑R' = (↑R , ↑r₀)

    -- rrmap from ↑R' to R'

    ↑R'-to-R' : rrmap ↑R' R'
    ↑R'-to-R' = (λ a b → lower) , (hrefl _)

    -- Lift Id

    ↑Id : A → A → 𝓤 ⊔ 𝓥 ̇
    ↑Id a b = Lift 𝓥 (a ≡ b)
    ↑Id' : refl-rel A (𝓤 ⊔ 𝓥)
    ↑Id' = (↑Id , λ a → lift (refl a))

    -- rrmap from ↑Id' to Id 

    ↑Id'-to-Id : rrmap ↑Id' (Id A , refl)
    ↑Id'-to-Id = (λ a b → lower) , (hrefl _)


    -- II. The statements

    i : 𝓤 ⊔ 𝓥 ⊔ 𝓦 ⁺ ̇
    i {𝓦} = is-id-system {𝓤} {𝓥} {𝓦} R'
    
    ii : 𝓤 ⊔ 𝓥 ⊔ 𝓦 ⁺ ̇
    ii {𝓦} = (a₀ : A) → is-based-id-system {𝓤} {𝓥} {𝓦} (R a₀ , r₀ a₀)
    
    iii : 𝓤 ⊔ 𝓥 ⊔ 𝓦 ⁺ ̇
    iii {𝓦} = (S' : refl-rel A 𝓦) → isContr (rrmap R' S')
    
    iv = (a b : A) → isequiv (λ (p : a ≡ b) → transport (R a) p (r₀ a))
    
    v = (a : A) → isContr (Σ b ꞉ A , R a b)


    -- III. Proof of the logical equivalences


    -- III.1. Identity systems are families of based identity systems
    
    i-to-ii : i {𝓤 ⊔ 𝓥 ⁺} → ii {𝓥}
    i-to-ii R'-is-id-system a₀ D d = (λ a r → f a₀ a r D d) , happly (happly (β-rule a₀) D) d where
      D⁺ : (a b : A) → R a b → 𝓤 ⊔ 𝓥 ⁺ ̇
      D⁺ a b r = (D' : (c : A) → R a c → 𝓥 ̇) → D' a (r₀ a) → D' b r
      f : (a b : A) (r : R a b) → D⁺ a b r
      f = pr₁ (R'-is-id-system D⁺ (λ a D' c → c))
      β-rule : (a : A) → f a a (r₀ a) ≡ (λ D' c → c)
      β-rule = pr₂ (R'-is-id-system D⁺ (λ a D' c → c))


    -- III.2. Families of based identity systems are identity systems

    ii-to-i : ii {𝓦} → i {𝓦}
    ii-to-i R'-is-based-id-system D d = (λ a → pr₁ (R'-is-based-id-system a (D a) (d a))) , (λ a → pr₂ (R'-is-based-id-system a (D a) (d a)))


    -- III.3. Families of based identity systems are initial reflexive relations
    
    ii-to-iii : ii {𝓦} → iii {𝓦}
    ii-to-iii R'-is-based-id-system (S , s₀) = ≃-preserves-Contr (ppmap-≃-rrmap R' (S , s₀)) (Π-preserves-Contr _ (λ a₀ → thm-5-8-2.i-to-ii (A , a₀) (R a₀ , r₀ a₀) (R'-is-based-id-system a₀) (S a₀ , s₀ a₀)))


    -- III.4. Identity systems are initial reflexive relations (CLEAN UP)

    i-to-iii : i {𝓦} → iii {𝓦}
    i-to-iii R'-is-id-system (S , s₀) =
      (f , fr) ,
      Σ-induction λ g gr → dpair-≡ (funext (λ a → funext λ b → funext λ r → α (g , gr) a b r) , (transport-lemma' (α (g , gr)) fr ∙ funext λ a → (ap _⁻¹ (pr₂ (R'-is-id-system (λ a b r → f a b r ≡ g a b r) (λ a → fr a ∙ (gr a) ⁻¹)) a) ∙ᵣ fr a) ∙ ((distr _ _ ∙ᵣ fr a) ∙ ∙-assoc _ _ _ ⁻¹ ∙ ((gr a ⁻¹) ⁻¹ ∙ₗ linv _) ∙ ru _ ⁻¹ ∙ ⁻¹-invol _)))
      where
      f : (a b : A) → R a b → S a b
      f = pr₁ (R'-is-id-system (λ a b r → S a b) s₀)
      fr : (a : A) → f a a (r₀ a) ≡ s₀ a
      fr = pr₂ (R'-is-id-system (λ a b r → S a b) s₀)
      α : (g' : rrmap R' (S , s₀)) (a b : A) (r : R a b) → f a b r ≡ pr₁ g' a b r
      α (g , gr) = pr₁ (R'-is-id-system (λ a b r → f a b r ≡ g a b r) (λ a → fr a ∙ (gr a) ⁻¹))
      transport-lemma : {f g : (a b : A) → R a b → S a b} (p : f ≡ g) (fr : (a : A) → f a a (r₀ a) ≡ s₀ a) → transport (λ - → (a : A) → - a a (r₀ a) ≡ s₀ a) p fr ≡ λ a → happly (happly (happly p a) a) (r₀ a) ⁻¹ ∙ fr a
      transport-lemma (refl _) fr₁ = funext (λ a → lu _)
      transport-lemma' : {f g : (a b : A) → R a b → S a b} (α : (a b : A) (r : R a b) → f a b r ≡ g a b r) (fr : (a : A) → f a a (r₀ a) ≡ s₀ a) → transport (λ - → (a : A) → - a a (r₀ a) ≡ s₀ a) (funext (λ a → funext λ b → funext λ r → α a b r)) fr ≡ λ a → α a a (r₀ a) ⁻¹ ∙ fr a
      transport-lemma' α₁ fr₁ = transport-lemma (funext (λ a → funext λ b → funext λ r → α₁ a b r)) fr₁ ∙ funext aux-path
        where
        aux-path : (a : A) → (happly (happly (happly (funext (λ a₁ → funext (λ b → funext (λ r → α₁ a₁ b r)))) a) a) (r₀ a) ⁻¹ ∙ fr₁ a) ≡ (α₁ a a (r₀ a) ⁻¹ ∙ fr₁ a)
        aux-path a rewrite
          happly-β (λ a₁ → funext (λ b → funext (λ r → α₁ a₁ b r))) a |
          happly-β (λ b → funext (λ r → α₁ a b r)) a |
          happly-β (λ r → α₁ a a r) (r₀ a) 
          = refl _

    
    -- III.5. If R' is an initial reflexive relation, then, for each a : A, transport (R a) - (r₀ a) is a fiberwise equivalence
    
    iii-to-iv : iii {𝓤 ⊔ 𝓥} → iv
    iii-to-iv R'-is-initial = λ a b → qinv-to-isequiv (pr₁ inv-rrmap a b , α' a b , β' a b)

      where

      -- Inverse rrmap

      inv-rrmap : rrmap R' (Id A , refl)
      inv-rrmap = ↑Id'-to-Id ∘rr pr₁ (R'-is-initial ↑Id')

      -- Right-invertibility

      aux-equiv : rrmap R' ↑R' ≃ rrmap R' R'
      aux-equiv = Σ-preserves-≃ _ _ (Π-preserves-family-≃ λ a → Π-preserves-family-≃ λ b → →-preserves-codom-≃ _ Lift-≃) λ g → Π-preserves-family-≃ (λ a → (ap lower) , ap-lower-is-equiv)

      rrmap-is-Contr : isContr (rrmap R' R')
      rrmap-is-Contr = ≃-preserves-Contr aux-equiv (R'-is-initial ↑R')

      α : ((λ a b p → transport (R a) p (r₀ a)) , hrefl r₀) ∘rr inv-rrmap ≡ rrmap-id R'
      α = pr₂ (pr₁ isContr-iff-is-inhabited-Prop rrmap-is-Contr) _ _
      α' : (a b : A) (r : R a b) → transport (R a) (pr₁ inv-rrmap a b r) (r₀ a) ≡ r
      α' = pr₁ (pr₁ (rrmap-≡ A R' R' (((λ a b p → transport (R a) p (r₀ a)) , hrefl r₀) ∘rr inv-rrmap) (rrmap-id R')) α)

      -- Left-invertibility

      β : inv-rrmap ∘rr ((λ a b p → transport (R a) p (r₀ a)) , hrefl r₀) ≡ rrmap-id (Id A , refl)
      β = pr₂ (rrendomap-Id-is-Contr A) _ ⁻¹
      β' : (a b : A) (p : a ≡ b) → pr₁ inv-rrmap a b (transport (R a) p (r₀ a)) ≡ p
      β' =  pr₁ (pr₁ (rrmap-≡ A (Id A , refl) (Id A , refl) (inv-rrmap ∘rr ((λ a b p → transport (R a) p (r₀ a)) , hrefl r₀)) (rrmap-id (Id A , refl))) β)
    

    -- III.6. If, for all a : A, transport (R a) - (r₀ a) is a fiberwise equivalence, then, for all a : A, Σ (R a) is contractible

    iv-to-v : iv → v
    iv-to-v transport-is-equiv a = thm-5-8-2.iii-to-iv (A , a) (R a , r₀ a) (transport-is-equiv a)


    -- III.7. If, for all a : A, Σ (R a) is contractible, then, for all a : A, (R a , r₀ a) is a based identity system.

    v-to-ii : v → ii {𝓦}
    v-to-ii ΣR-is-Contr a₀ = thm-5-8-2.iv-to-i (A , a₀) (R a₀ , r₀ a₀) (ΣR-is-Contr a₀)

    -- III.8. Other implications

    iv-to-i : iv → i {𝓦}
    iv-to-i = ii-to-i ∘ v-to-ii ∘ iv-to-v


  -- Corollary 5.8.5 (Equivalence induction)

  module equivalence-induction ⦃ fe : FunExt ⦄ ⦃ univ : Univalence ⦄ where

    idtoeqv' : {A B : 𝓤 ̇} → (A ≡ B) → (A ≃ B)
    idtoeqv' {𝓤} {A} {B} p = transport (λ B → A ≃ B) p (≃-refl A)

    idtoeqv-agreement : {A B : 𝓤 ̇} → idtoeqv {𝓤} {A} {B} ∼ idtoeqv' {𝓤} {A} {B}
    idtoeqv-agreement (refl _) = refl _ 

    idtoeqv'-is-equiv : {A B : 𝓤 ̇} → isequiv (idtoeqv' {𝓤} {A} {B})
    idtoeqv'-is-equiv = transport isequiv (funext idtoeqv-agreement) idtoeqv-is-equiv 

    ≃-is-id-system : is-id-system {𝓤 ⁺} {𝓤} {𝓥} (_≃_ {𝓤} {𝓤} , ≃-refl)
    ≃-is-id-system {𝓤} {𝓥} = thm-5-8-4.iv-to-i (𝓤 ̇) (_≃_ {𝓤} {𝓤} , ≃-refl) (λ A B → idtoeqv'-is-equiv)

    𝕁-≃ : (D : (A B : 𝓤 ̇) → A ≃ B → 𝓥 ̇) → ((A : 𝓤 ̇) → D A A (≃-refl A)) → (A B : 𝓤 ̇) (e : A ≃ B) → D A B e
    𝕁-≃ D d = pr₁ (≃-is-id-system D d)

    𝕁-≃-β : (D : (A B : 𝓤 ̇) (e : A ≃ B) → 𝓥 ̇) (d : (A : 𝓤 ̇) → D A A (≃-refl A)) (A : 𝓤 ̇) → 𝕁-≃ D d A A (≃-refl A) ≡ d A
    𝕁-≃-β D d = pr₂ (≃-is-id-system D d)

    ≃-is-based-id-system : (A : 𝓤 ̇) → is-based-id-system {𝓤 ⁺} {𝓤} {𝓥} ((A ≃_) , ≃-refl A)
    ≃-is-based-id-system {𝓤} {𝓥} A = thm-5-8-2.iii-to-i ((𝓤 ̇) , A) ((A ≃_) , ≃-refl A) (λ B → idtoeqv'-is-equiv)

    ℍ-≃ : (A : 𝓤 ̇) (D : (B : 𝓤 ̇) → A ≃ B → 𝓥 ̇) → D A (≃-refl A) → (B : 𝓤 ̇) (e : A ≃ B) → D B e
    ℍ-≃ A D d = pr₁ (≃-is-based-id-system A D d)

    ℍ-≃-β : (A : 𝓤 ̇) (D : (B : 𝓤 ̇) → A ≃ B → 𝓥 ̇) (d : D A (≃-refl A)) → ℍ-≃ A D d A (≃-refl A) ≡ d
    ℍ-≃-β A D d = pr₂ (≃-is-based-id-system A D d)

  open equivalence-induction using (𝕁-≃ ; 𝕁-≃-β ; ℍ-≃ ; ℍ-≃-β) public

--   module based-equivalence-induction ⦃ fe : FunExt ⦄ ⦃ univ : Univalence ⦄ where

--     ≃-is-based-id-system : is-based-id-system


--   -- Corollary 5.8.6 (Homotopy induction)

--   module homotopy-induction ⦃ fe : FunExt ⦄ where

-- --     happly' : {A : 𝓤 ̇} {B : A → 𝓥 ̇} {f g ꞉ Π B} → f ≡ g → f ∼ g
-- --     happly' = ?


-- -- -- happly : {A : 𝓤 ̇ } {B : A → 𝓥 ̇ } {f g : Π B} → f ≡ g → f ∼ g
-- -- -- happly (refl f) x = refl (f x)

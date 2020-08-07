{-# OPTIONS --without-K --exact-split --safe #-}

open import Ch1.Type-theory
open import Ch2.Homotopy-type-theory
open import Ch3.Sets-and-logic
open import Ch4.Equivalences

module Ch5.8-Id-types-and-id-systems where


module single-universe where

  -- Definition 5.8.1 (Pointed predicate, pointed family of maps, based identity system).

  pted-pred : 𝓤 ⊙ → 𝓤 ⁺ ̇
  pted-pred {𝓤} (A , a₀) = Σ R ꞉ (A → 𝓤 ̇) , R a₀

  ppmap : (A : 𝓤 ⊙) → pted-pred A → pted-pred A → 𝓤 ̇
  ppmap (A , a₀) (R , r₀) (S , s₀) = Σ g ꞉ Π (λ a → R a → S a) , g a₀ r₀ ≡ s₀ 

  is-based-id-system : {A : 𝓤 ⊙} → pted-pred A  → 𝓤 ⁺ ̇
  is-based-id-system {𝓤} {A , a₀} (R , r₀) = (D : (a : A) → R a → 𝓤 ̇) (d : D a₀ r₀) → Σ f ꞉ ((a : A) (r : R a) → D a r) , f a₀ r₀ ≡ d


  -- Composition of pointed families of maps

  ppmap-comp : (A : 𝓤 ⊙) (R S T : pted-pred A) → ppmap A R S → ppmap A S T → ppmap A R T
  ppmap-comp (A , a₀) (R , r₀) (S , s₀) (T , t₀) (f , fr) (g , gr) = (λ a → g a ∘ f a) , (ap (g a₀) fr ∙ gr)


  -- Identity pointed familiy of maps

  ppmap-id : (A : 𝓤 ⊙) (R : pted-pred A) → ppmap A R R
  ppmap-id (A , a₀) (R , r₀) = (λ a → id) , (refl r₀)


  -- Identity type of pointed families of maps

  ppmap-≡ : ⦃ fe : FunExt ⦄ (A : 𝓤 ⊙) (R : pted-pred A) (S : pted-pred A) (g h : ppmap A R S) → (g ≡ h) ≃ (Σ α ꞉ ((a : pr₁ A) (r : pr₁ R a) → pr₁ g a r ≡ pr₁ h a r) , (α (pr₂ A) (pr₂ R) ⁻¹ ∙ pr₂ g ≡ pr₂ h))
  ppmap-≡ (A , a₀) (R , r₀) (S , s₀) (g , gr) (h , hr) = Σ-≡-equiv ● Σ-preserves-≃ _ _ ((happly , happly-is-equiv) ● Π-preserves-family-≃ (λ a → happly , happly-is-equiv)) λ p → (path p gr ⁻¹ ∙_ ) , (qinv-to-isequiv (qinv-pre-∙ hr (path p gr ⁻¹))) where
    path : {g h : Π λ a → R a → S a} (p : g ≡ h) (gr : g a₀ r₀ ≡ s₀) → transport (λ - → (- a₀ r₀) ≡ s₀) p gr ≡ happly (happly p a₀) r₀ ⁻¹ ∙ gr  
    path (refl _) gr = lu _


  -- Theorem 5.8.2 (Fundamental theorem of based identity types).

  module thm-5-8-2 ⦃ fe : FunExt ⦄ (A' : 𝓤 ⊙) (R' : pted-pred A') where

  -- Unfold the pointed type and predicate

    A = pr₁ A'
    a₀ = pr₂ A'
    R = pr₁ R'
    r₀ = pr₂ R'

    -- TFAE

    i = is-based-id-system R'
    ii = (S' : pted-pred A') → isContr (ppmap A' R' S')
    iii = (a : A) → isequiv (λ (- : a₀ ≡ a) → transport R - r₀)
    iv = isContr (Σ R)

    -- The statements are propositions (the proof of i-is-Prop is omitted).

    ii-is-Prop : isProp ii
    ii-is-Prop = Π-preserves-Props _ (λ S' → isContr-is-Prop _)

    iii-is-Prop : isProp iii
    iii-is-Prop = Π-preserves-Props _ (λ a → ishae-is-Prop _)

    iv-is-Prop : isProp iv
    iv-is-Prop = isContr-is-Prop _

    -- Proof of the logical equivalences

    i-to-ii : i → ii
    i-to-ii R'-is-based-id-system (S , s₀) = pr₂ isContr-iff-is-inhabited-Prop (inhabited , is-Prop) where
      inhabited : ppmap A' R' (S , s₀)
      inhabited = R'-is-based-id-system (λ a r → S a) s₀
      is-Prop : isProp (ppmap A' R' (S , s₀))
      is-Prop (f , fr) (g , gr) =
        let R'-ind = R'-is-based-id-system (λ a r → f a r ≡ g a r) (fr ∙ gr ⁻¹)
        in inv (ppmap-≡ A' R' (S , s₀) (f , fr) (g , gr)) (
          pr₁ R'-ind ,
          (((ap _⁻¹ (pr₂ (R'-ind)) ∙ distr _ _) ∙ᵣ fr) ∙ (∙-assoc _ _ _ ⁻¹ ∙ (ap (λ - → (gr ⁻¹) ⁻¹ ∙ -) (linv _) ∙ ru _ ⁻¹ ∙ ⁻¹-invol _)))
          )

    ii-to-iii : ii → iii
    ii-to-iii R'-is-initial = λ a → qinv-to-isequiv (pr₁ inv-ppmap a , α' a , β' a)
      where

      -- Identity is a pointed predicate

      S : A → 𝓤 ̇
      S a = a₀ ≡ a
      s₀ : S a₀
      s₀ = refl a₀
      S' : pted-pred A'
      S' = (S , s₀)

      -- Inverse pointed family of maps

      Contr₁ : isContr (ppmap A' R' S')
      Contr₁ = R'-is-initial S'
      inv-ppmap : ppmap A' R' S' 
      inv-ppmap = pr₁ Contr₁

      -- Right-invertibility

      Contr₂ : isContr (ppmap A' R' R')
      Contr₂ = R'-is-initial R'
      α : ppmap-comp A' R' S' R' inv-ppmap ((λ a p → transport R p r₀) , refl r₀) ≡ ppmap-id A' R'
      α = pr₂ (pr₁ isContr-iff-is-inhabited-Prop Contr₂) _ _
      α' : (a : A) (r : R a) → transport R (pr₁ inv-ppmap a r) r₀ ≡ r
      α' = pr₁ (pr₁ (ppmap-≡ A' R' R' (ppmap-comp A' R' S' R' inv-ppmap ((λ a p → transport R p r₀) , refl r₀)) (ppmap-id A' R')) α)

      -- Left-invertibility

      Contr₃ : isContr (ppmap A' S' S')
      Contr₃ = ppmap-id A' S' , Σ-induction (λ f fr → inv (ppmap-≡ A' S' S' (ppmap-id A' S') (f , fr)) ((ℍ a₀ (λ a p → pr₁ (ppmap-id A' S') a p ≡ f a p) (fr ⁻¹)) , (ru _ ⁻¹ ∙ ⁻¹-invol _)))
      β : ppmap-comp A' S' R' S' ((λ a p → transport R p r₀) , refl r₀) inv-ppmap ≡ ppmap-id A' S'
      β = pr₂ Contr₃ _ ⁻¹
      β' : (a : A) (p : S a) → pr₁ inv-ppmap a (transport R p r₀) ≡ p
      β' = pr₁ (pr₁ (ppmap-≡ A' S' S' (ppmap-comp A' S' R' S' ((λ a p → transport R p r₀) , refl r₀) inv-ppmap) (ppmap-id A' S')) β)


    iii-to-iv : iii → iv
    iii-to-iv transport-is-equiv = ≃-preserves-Contr (Σ-preserves-family-≃ (λ a → (λ (p : a₀ ≡ a) → transport R p r₀) , transport-is-equiv a)) (free-right-endpt-is-Contr A a₀)


    iv-to-i : iv → i
    iv-to-i ΣR-is-Contr D d = (curry (λ u → transport (Σ-induction D) (p u) d)) , (ap (λ - → transport (Σ-induction D) - d) q) where
      p : (u : Σ R) → (a₀ , r₀) ≡ u
      p = pr₂ (pr₁ isContr-iff-is-inhabited-Prop ΣR-is-Contr) (a₀ , r₀)
      q : p (a₀ , r₀) ≡ refl (a₀ , r₀)
      q = pr₂ (pr₁ isContr-iff-is-inhabited-Prop (pr₁ (Prop-iff-Contr-≡ (Σ R)) (pr₂ (pr₁ isContr-iff-is-inhabited-Prop ΣR-is-Contr)) (a₀ , r₀) (a₀ , r₀))) _ _ 


module multiple-universes where

  -- Definition 5.8.1 (Pointed predicate, pointed family of maps, based identity system).

  pted-pred : 𝓤 ⊙ → (𝓥 : Universe) → 𝓤 ⊔ 𝓥 ⁺ ̇
  pted-pred {𝓤} (A , a₀) 𝓥 = Σ R ꞉ (A → 𝓥 ̇) , R a₀

  ppmap : (A : 𝓤 ⊙) → pted-pred A 𝓥 → pted-pred A 𝓦 → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ̇
  ppmap (A , a₀) (R , r₀) (S , s₀) = Σ g ꞉ Π (λ a → R a → S a) , g a₀ r₀ ≡ s₀ 

  is-based-id-system : {A : 𝓤 ⊙} → pted-pred A 𝓥 → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ⁺ ̇ 
  is-based-id-system {𝓤} {𝓥} {𝓦} {A , a₀} (R , r₀) = (D : (a : A) → R a → 𝓦 ̇) (d : D a₀ r₀) → Σ f ꞉ ((a : A) (r : R a) → D a r) , f a₀ r₀ ≡ d


  -- Composition of pointed families of maps

  ppmap-comp : (A : 𝓤 ⊙) (R : pted-pred A 𝓥) (S : pted-pred A 𝓦) (T : pted-pred A 𝓣) → ppmap A R S → ppmap A S T → ppmap A R T
  ppmap-comp (A , a₀) (R , r₀) (S , s₀) (T , t₀) (f , fr) (g , gr) = (λ a → g a ∘ f a) , (ap (g a₀) fr ∙ gr)


  -- Identity pointed family of maps

  ppmap-id : (A : 𝓤 ⊙) (R : pted-pred A 𝓥) → ppmap A R R
  ppmap-id (A , a₀) (R , r₀) = (λ a → id) , (refl r₀)


  -- Identity type of pointed families of maps

  ppmap-≡ : ⦃ fe : FunExt ⦄ (A : 𝓤 ⊙) (R : pted-pred A 𝓥) (S : pted-pred A 𝓦) (g h : ppmap A R S) → (g ≡ h) ≃ (Σ α ꞉ ((a : pr₁ A) (r : pr₁ R a) → pr₁ g a r ≡ pr₁ h a r) , (α (pr₂ A) (pr₂ R) ⁻¹ ∙ pr₂ g ≡ pr₂ h))
  ppmap-≡ (A , a₀) (R , r₀) (S , s₀) (g , gr) (h , hr) = Σ-≡-equiv ● Σ-preserves-≃ _ _ ((happly , happly-is-equiv) ● Π-preserves-family-≃ (λ a → happly , happly-is-equiv)) λ p → (path p gr ⁻¹ ∙_ ) , (qinv-to-isequiv (qinv-pre-∙ hr (path p gr ⁻¹))) where
     path : {g h : Π λ a → R a → S a} (p : g ≡ h) (gr : g a₀ r₀ ≡ s₀) → transport (λ - → (- a₀ r₀) ≡ s₀) p gr ≡ happly (happly p a₀) r₀ ⁻¹ ∙ gr  
     path (refl _) gr = lu _


  -- Theorem 5.8.2 (Fundamental theorem of based identity types).

  module thm-5-8-2 ⦃ fe : FunExt ⦄ (A' : 𝓤 ⊙) (R' : pted-pred A' 𝓥) where

    -- Unfold the pointed type and predicate

    A = pr₁ A'
    a₀ = pr₂ A'
    R = pr₁ R'
    r₀ = pr₂ R'

    -- TFAE

    i : 𝓤 ⊔ 𝓥 ⊔ 𝓦 ⁺ ̇
    i {𝓦} = is-based-id-system {𝓤} {𝓥} {𝓦} R'
    ii : 𝓤 ⊔ 𝓥 ⊔ 𝓦 ⁺ ̇
    ii {𝓦} = (S' : pted-pred A' 𝓦) → isContr (ppmap A' R' S')
    iii = (a : A) → isequiv (λ (- : a₀ ≡ a) → transport R - r₀)
    iv = isContr (Σ R)

    -- The statements are propositions (the proof of i-is-Prop is omitted).

    ii-is-Prop : isProp (ii {𝓦})
    ii-is-Prop = Π-preserves-Props _ (λ S' → isContr-is-Prop _)

    iii-is-Prop : isProp iii
    iii-is-Prop = Π-preserves-Props _ (λ a → ishae-is-Prop _)

    iv-is-Prop : isProp iv
    iv-is-Prop = isContr-is-Prop _

    -- Proof of the logical equivalences.

    i-to-ii : i {𝓦} → ii {𝓦}
    i-to-ii R'-is-based-id-system (S , s₀) = pr₂ isContr-iff-is-inhabited-Prop (inhabited , is-Prop) where
      inhabited : ppmap A' R' (S , s₀)
      inhabited = R'-is-based-id-system (λ a r → S a) s₀
      is-Prop : isProp (ppmap A' R' (S , s₀))
      is-Prop (f , fr) (g , gr) =
        let R'-ind = R'-is-based-id-system (λ a r → f a r ≡ g a r) (fr ∙ gr ⁻¹)
        in inv (ppmap-≡ A' R' (S , s₀) (f , fr) (g , gr)) (
          pr₁ R'-ind ,
          (((ap _⁻¹ (pr₂ (R'-ind)) ∙ distr _ _) ∙ᵣ fr) ∙ (∙-assoc _ _ _ ⁻¹ ∙ (ap (λ - → (gr ⁻¹) ⁻¹ ∙ -) (linv _) ∙ ru _ ⁻¹ ∙ ⁻¹-invol _)))
          )

    ii-to-ii : ii {𝓤 ⊔ 𝓥 ⊔ 𝓦} → ii {𝓤 ⊔ 𝓥}
    ii-to-ii {𝓦} R'-is-initial (S , s₀) = ≃-preserves-Contr aux-equiv Contr
      where

      S' : pted-pred A' (𝓤 ⊔ 𝓥)
      S' = (S , s₀)

      -- Lifting (S , s₀)
      
      LS : A → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ̇
      LS = Lift 𝓦 ∘ S
      ls₀ : LS a₀
      ls₀ = lift s₀
      LS' : pted-pred A' (𝓤 ⊔ 𝓥 ⊔ 𝓦)
      LS' = (LS , ls₀)

      -- Pointed map from LS' to S

      LS'-to-S' : ppmap A' LS' S'
      LS'-to-S' = (λ a → lower) , refl _

      -- Equivalence of ppmap spaces

      Contr : isContr (ppmap A' R' LS')
      Contr = R'-is-initial LS'
      aux-equiv : ppmap A' R' LS' ≃ ppmap A' R' S'
      aux-equiv = Σ-preserves-≃ _ _ (Π-preserves-family-≃ (λ a → →-preserves-codom-≃ _ (lower , (qinv-to-isequiv (lift , hrefl _ , hrefl _))))) (λ g → ap lower , ap-of-equiv-is-equiv (qinv-to-isequiv (lift , hrefl _  , hrefl _)) _ _)


    ii-to-iii : ii {𝓤 ⊔ 𝓥} → iii
    ii-to-iii R'-is-initial = λ a → qinv-to-isequiv (pr₁ inv-ppmap a , α' a , β' a)
      where

      -- Lifting R'

      LR : A → 𝓤 ⊔ 𝓥 ̇
      LR = Lift 𝓤 ∘ R
      lr₀ : LR a₀
      lr₀ = lift r₀
      LR' : pted-pred A' (𝓤 ⊔ 𝓥)
      LR' = (LR , lr₀)

      -- Pointed map from LR' to R'

      LR'-to-R' : ppmap A' LR' R'
      LR'-to-R' = (λ a → lower) , refl _

      -- Identity is a pointed predicate

      S : A → 𝓤 ̇
      S a = a₀ ≡ a
      s₀ : S a₀
      s₀ = refl a₀
      S' : pted-pred A' 𝓤
      S' = (S , s₀)

      -- Lifting the identity predicate

      LS : A → 𝓤 ⊔ 𝓥 ̇
      LS a = Lift 𝓥 (a₀ ≡ a)
      ls₀ : LS a₀
      ls₀ = lift (refl a₀)
      LS' : pted-pred A' (𝓤 ⊔ 𝓥)
      LS' = (LS , ls₀)

      -- Pointed map from LS' to S

      LS'-to-S' : ppmap A' LS' S'
      LS'-to-S' = (λ a → lower) , refl _

      -- Inverse pointed family of maps

      Contr₁ : isContr (ppmap A' R' LS')
      Contr₁ = R'-is-initial LS'
      inv-ppmap : ppmap A' R' S' 
      inv-ppmap = ppmap-comp A' R' LS' S' (pr₁ Contr₁) LS'-to-S'

      -- Right-invertibility

      Contr₂' : isContr (ppmap A' R' LR')
      Contr₂' = R'-is-initial LR'
      aux-equiv : ppmap A' R' LR' ≃ ppmap A' R' R'
      aux-equiv = Σ-preserves-≃ _ _ (Π-preserves-family-≃ (λ a → →-preserves-codom-≃ _ (lower , (qinv-to-isequiv (lift , hrefl _ , hrefl _))))) (λ g → ap lower , ap-of-equiv-is-equiv (qinv-to-isequiv (lift , hrefl _  , hrefl _)) _ _)
      Contr₂ : isContr (ppmap A' R' R')
      Contr₂ = ≃-preserves-Contr aux-equiv Contr₂'
      α : ppmap-comp A' R' S' R' inv-ppmap ((λ a p → transport R p r₀) , refl r₀) ≡ ppmap-id A' R'
      α = pr₂ (pr₁ isContr-iff-is-inhabited-Prop Contr₂) _ _
      α' : (a : A) (r : R a) → transport R (pr₁ inv-ppmap a r) r₀ ≡ r
      α' = pr₁ (pr₁ (ppmap-≡ A' R' R' (ppmap-comp A' R' S' R' inv-ppmap ((λ a p → transport R p r₀) , refl r₀)) (ppmap-id A' R')) α)

      -- Left-invertibility

      Contr₃ : isContr (ppmap A' S' S')
      Contr₃ = ppmap-id A' S' , Σ-induction (λ f fr → inv (ppmap-≡ A' S' S' (ppmap-id A' S') (f , fr)) ((ℍ a₀ (λ a p → pr₁ (ppmap-id A' S') a p ≡ f a p) (fr ⁻¹)) , (ru _ ⁻¹ ∙ ⁻¹-invol _)))
      β : ppmap-comp A' S' R' S' ((λ a p → transport R p r₀) , refl r₀) inv-ppmap ≡ ppmap-id A' S'
      β = pr₂ Contr₃ _ ⁻¹
      β' : (a : A) (p : S a) → pr₁ inv-ppmap a (transport R p r₀) ≡ p
      β' = pr₁ (pr₁ (ppmap-≡ A' S' S' (ppmap-comp A' S' R' S' ((λ a p → transport R p r₀) , refl r₀) inv-ppmap) (ppmap-id A' S')) β)


    iii-to-iv : iii → iv
    iii-to-iv transport-is-equiv = ≃-preserves-Contr (Σ-preserves-family-≃ (λ a → (λ (p : a₀ ≡ a) → transport R p r₀) , transport-is-equiv a)) (free-right-endpt-is-Contr A a₀)


    iv-to-i : iv → i {𝓦}
    iv-to-i ΣR-is-Contr D d = (curry (λ u → transport (Σ-induction D) (p u) d)) , (ap (λ - → transport (Σ-induction D) - d) q) where
      p : (u : Σ R) → (a₀ , r₀) ≡ u
      p = pr₂ (pr₁ isContr-iff-is-inhabited-Prop ΣR-is-Contr) (a₀ , r₀)
      q : p (a₀ , r₀) ≡ refl (a₀ , r₀)
      q = pr₂ (pr₁ isContr-iff-is-inhabited-Prop (pr₁ (Prop-iff-Contr-≡ (Σ R)) (pr₂ (pr₁ isContr-iff-is-inhabited-Prop ΣR-is-Contr)) (a₀ , r₀) (a₀ , r₀))) _ _ 


  -- Definition 5.8.3 (identity system)

  is-id-system : {A : 𝓤 ̇} → (Σ R ꞉ (A → A → 𝓥 ̇) , ((a : A) → R a a)) → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ⁺ ̇
  is-id-system {𝓤} {𝓥} {𝓦} {A} (R , r₀) = (D : (a b : A) → R a b → 𝓦 ̇) (d : (a : A) → D a a (r₀ a)) → Σ f ꞉ ((a b : A) (r : R a b) → D a b r) , ((a : A) → f a a (r₀ a) ≡ d a)


  -- Theorem 5.8.4. (Fundamental theorem of identity types).

  module thm-5-8-4 ⦃ fe : FunExt ⦄ (A : 𝓤 ̇) (R' : (Σ R ꞉ (A → A → 𝓥 ̇) , ((a : A) → R a a))) where

    -- Unfold R'

    R = pr₁ R'
    r₀ = pr₂ R'

    -- TFAE

    i : 𝓤 ⊔ 𝓥 ⊔ 𝓦 ⁺ ̇
    i {𝓦} = is-id-system {𝓤} {𝓥} {𝓦} R'
    ii : 𝓤 ⊔ 𝓥 ⊔ 𝓦 ⁺ ̇
    ii {𝓦} = (a₀ : A) → is-based-id-system {𝓤} {𝓥} {𝓦} (R a₀ , r₀ a₀)
    iii : 𝓤 ⊔ 𝓥 ⊔ 𝓦 ⁺ ̇
    iii {𝓦} = (S' : (Σ S ꞉ (A → A → 𝓦 ̇) , ((a : A) → S a a))) → isContr (Σ g ꞉ ((a b : A) → R a b → pr₁ S' a b) , ((a : A) → g a a (r₀ a) ≡ pr₂ S' a))
    iv = (a b : A) → isequiv (λ (p : a ≡ b) → transport (R a) p (r₀ a))
    v = (a : A) → isContr (Σ b ꞉ A , R a b)

    -- Proof of the logical equivalences

    i-to-ii : i {𝓤 ⊔ 𝓥 ⁺} → ii {𝓥}
    i-to-ii R'-is-id-system a₀ D d = (λ a r → f a₀ a r D d) , happly (happly (β-rule a₀) D) d where
      D⁺ : (a b : A) → R a b → 𝓤 ⊔ 𝓥 ⁺ ̇
      D⁺ a b r = (D' : (c : A) → R a c → 𝓥 ̇) → D' a (r₀ a) → D' b r
      f : (a b : A) (r : R a b) → D⁺ a b r
      f = pr₁ (R'-is-id-system D⁺ (λ a D' c → c))
      β-rule : (a : A) → f a a (r₀ a) ≡ (λ D' c → c)
      β-rule = pr₂ (R'-is-id-system D⁺ (λ a D' c → c))

    ii-to-i : ii {𝓦} → i {𝓦}
    ii-to-i R'-is-based-id-system D d = (λ a → pr₁ (R'-is-based-id-system a (D a) (d a))) , (λ a → pr₂ (R'-is-based-id-system a (D a) (d a)))

    -- It seems like i and ii can only be equivalent globally or with some form of impredicativity.

    i-to-iii : i {𝓦} → iii {𝓦}
    i-to-iii R'-is-id-system (S , s₀) =
      (f , fr) ,
      Σ-induction λ g gr → dpair-≡ (funext (λ a → funext λ b → funext λ r → α (g , gr) a b r) , (transport-lemma' (α (g , gr)) fr ∙ funext λ a → (ap _⁻¹ (pr₂ (R'-is-id-system (λ a b r → f a b r ≡ g a b r) (λ a → fr a ∙ (gr a) ⁻¹)) a) ∙ᵣ fr a) ∙ ((distr _ _ ∙ᵣ fr a) ∙ ∙-assoc _ _ _ ⁻¹ ∙ ((gr a ⁻¹) ⁻¹ ∙ₗ linv _) ∙ ru _ ⁻¹ ∙ ⁻¹-invol _)))
      where
      f : (a b : A) → R a b → S a b
      f = pr₁ (R'-is-id-system (λ a b r → S a b) s₀)
      fr : (a : A) → f a a (r₀ a) ≡ s₀ a
      fr = pr₂ (R'-is-id-system (λ a b r → S a b) s₀)
      α : (g' : Σ g ꞉ ((a b : A) → R a b → S a b) , ((a : A) → g a a (r₀ a) ≡ s₀ a)) (a b : A) (r : R a b) → f a b r ≡ pr₁ g' a b r
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

    -- iii-to-i : iii {𝓦} → i {𝓦}
    -- iii-to-i Contr D d = {!!} , {!!}

    -- etc.
  

-- -- Corollary 5.8.5 (Equivalence induction)

-- 𝕁-≃ : (D : (A B : 𝓤 ̇) (e : A ≃ B) → 𝓥 ̇) ( (A B : 𝓤 ̇) (e : A ≃ B) →  



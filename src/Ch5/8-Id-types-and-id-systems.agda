{-# OPTIONS --without-K --exact-split --safe #-}

open import Ch1.Type-theory
open import Ch2.Homotopy-type-theory
open import Ch3.Sets-and-logic
open import Ch4.Equivalences

module Ch5.8-Id-types-and-id-systems where


-- -- Definition 5.8.1 (Pointed predicate, pointed family of maps, based identity system).

-- pted-pred : 𝓤 ⊙ → 𝓤 ⁺ ̇
-- pted-pred {𝓤} (A , a₀) = Σ R ꞉ (A → 𝓤 ̇) , R a₀

-- ppmap : (A : 𝓤 ⊙) → pted-pred A → pted-pred A → 𝓤 ̇
-- ppmap (A , a₀) (R , r₀) (S , s₀) = Σ g ꞉ Π (λ a → R a → S a) , g a₀ r₀ ≡ s₀ 

-- is-based-id-system : {A : 𝓤 ⊙} → pted-pred A  → 𝓤 ⁺ ̇
-- is-based-id-system {𝓤} {A , a₀} (R , r₀) = (D : (a : A) → R a → 𝓤 ̇) (d : D a₀ r₀) → Σ f ꞉ ((a : A) (r : R a) → D a r) , f a₀ r₀ ≡ d


-- -- Composition of pointed families of maps

-- ppmap-comp : (A : 𝓤 ⊙) (R S T : pted-pred A) → ppmap A R S → ppmap A S T → ppmap A R T
-- ppmap-comp (A , a₀) (R , r₀) (S , s₀) (T , t₀) (f , fr) (g , gr) = (λ a → g a ∘ f a) , (ap (g a₀) fr ∙ gr)


-- -- Identity pointed familiy of maps

-- ppmap-id : (A : 𝓤 ⊙) (R : pted-pred A) → ppmap A R R
-- ppmap-id (A , a₀) (R , r₀) = (λ a → id) , (refl r₀)


-- -- Identity type of pointed families of maps

-- ppmap-≡ : ⦃ fe : FunExt ⦄ (A : 𝓤 ⊙) (R : pted-pred A) (S : pted-pred A) (g h : ppmap A R S) → (g ≡ h) ≃ (Σ α ꞉ ((a : pr₁ A) (r : pr₁ R a) → pr₁ g a r ≡ pr₁ h a r) , (α (pr₂ A) (pr₂ R) ⁻¹ ∙ pr₂ g ≡ pr₂ h))
-- ppmap-≡ (A , a₀) (R , r₀) (S , s₀) (g , gr) (h , hr) = Σ-≡-equiv ● Σ-preserves-≃ _ _ ((happly , happly-is-equiv) ● Π-preserves-family-≃ (λ a → happly , happly-is-equiv)) λ p → (path p gr ⁻¹ ∙_ ) , (qinv-to-isequiv (qinv-pre-∙ hr (path p gr ⁻¹))) where
--   path : {g h : Π λ a → R a → S a} (p : g ≡ h) (gr : g a₀ r₀ ≡ s₀) → transport (λ - → (- a₀ r₀) ≡ s₀) p gr ≡ happly (happly p a₀) r₀ ⁻¹ ∙ gr  
--   path (refl _) gr = lu _


-- -- Theorem 5.8.2 (Fundamental theorem of based identity types).

-- module thm-5-8-2 ⦃ fe : FunExt ⦄ (A' : 𝓤 ⊙) (R' : pted-pred A') where

-- -- Unfold the pointed type and predicate

--   A = pr₁ A'
--   a₀ = pr₂ A'
--   R = pr₁ R'
--   r₀ = pr₂ R'

--   -- TFAE

--   i = is-based-id-system R'
--   ii = (S' : pted-pred A') → isContr (ppmap A' R' S')
--   iii = (a : A) → isequiv (λ (- : a₀ ≡ a) → transport R - r₀)
--   iv = isContr (Σ R)

--   -- The statements are propositions (the proof of i-is-Prop is omitted).

--   ii-is-Prop : isProp ii
--   ii-is-Prop = Π-preserves-Props _ (λ S' → isContr-is-Prop _)

--   iii-is-Prop : isProp iii
--   iii-is-Prop = Π-preserves-Props _ (λ a → ishae-is-Prop _)

--   iv-is-Prop : isProp iv
--   iv-is-Prop = isContr-is-Prop _

--   -- Proof of the logical equivalences

--   i-to-ii : i → ii
--   i-to-ii R'-is-based-id-system (S , s₀) = pr₂ isContr-iff-is-inhabited-Prop (inhabited , is-Prop) where
--     inhabited : ppmap A' R' (S , s₀)
--     inhabited = R'-is-based-id-system (λ a r → S a) s₀
--     is-Prop : isProp (ppmap A' R' (S , s₀))
--     is-Prop (f , fr) (g , gr) =
--       let R'-ind = R'-is-based-id-system (λ a r → f a r ≡ g a r) (fr ∙ gr ⁻¹)
--       in inv (ppmap-≡ A' R' (S , s₀) (f , fr) (g , gr)) (
--         pr₁ R'-ind ,
--         (((ap _⁻¹ (pr₂ (R'-ind)) ∙ distr _ _) ∙ᵣ fr) ∙ (∙-assoc _ _ _ ⁻¹ ∙ (ap (λ - → (gr ⁻¹) ⁻¹ ∙ -) (linv _) ∙ ru _ ⁻¹ ∙ ⁻¹-invol _)))
--         )

--   ii-to-iii : ii → iii
--   ii-to-iii R'-is-initial = λ a → qinv-to-isequiv (pr₁ inv-ppmap a , α' a , β' a)
--     where

--     -- Identity is a pointed predicate
    
--     S : A → 𝓤 ̇
--     S a = a₀ ≡ a
--     s₀ : S a₀
--     s₀ = refl a₀
--     S' : pted-pred A'
--     S' = (S , s₀)

--     -- Inverse pointed family of maps

--     Contr₁ : isContr (ppmap A' R' S')
--     Contr₁ = R'-is-initial S'
--     inv-ppmap : ppmap A' R' S' 
--     inv-ppmap = pr₁ Contr₁

--     -- Right-invertibility

--     Contr₂ : isContr (ppmap A' R' R')
--     Contr₂ = R'-is-initial R'
--     α : ppmap-comp A' R' S' R' inv-ppmap ((λ a p → transport R p r₀) , refl r₀) ≡ ppmap-id A' R'
--     α = pr₂ (pr₁ isContr-iff-is-inhabited-Prop Contr₂) _ _
--     α' : (a : A) (r : R a) → transport R (pr₁ inv-ppmap a r) r₀ ≡ r
--     α' = pr₁ (pr₁ (ppmap-≡ A' R' R' (ppmap-comp A' R' S' R' inv-ppmap ((λ a p → transport R p r₀) , refl r₀)) (ppmap-id A' R')) α)

--     -- Left-invertibility

--     Contr₃ : isContr (ppmap A' S' S')
--     Contr₃ = ppmap-id A' S' , Σ-induction (λ f fr → inv (ppmap-≡ A' S' S' (ppmap-id A' S') (f , fr)) ((ℍ a₀ (λ a p → pr₁ (ppmap-id A' S') a p ≡ f a p) (fr ⁻¹)) , (ru _ ⁻¹ ∙ ⁻¹-invol _)))
--     β : ppmap-comp A' S' R' S' ((λ a p → transport R p r₀) , refl r₀) inv-ppmap ≡ ppmap-id A' S'
--     β = pr₂ Contr₃ _ ⁻¹
--     β' : (a : A) (p : S a) → pr₁ inv-ppmap a (transport R p r₀) ≡ p
--     β' = pr₁ (pr₁ (ppmap-≡ A' S' S' (ppmap-comp A' S' R' S' ((λ a p → transport R p r₀) , refl r₀) inv-ppmap) (ppmap-id A' S')) β)
    

--   iii-to-iv : iii → iv
--   iii-to-iv transport-is-equiv = ≃-preserves-Contr (Σ-preserves-family-≃ (λ a → (λ (p : a₀ ≡ a) → transport R p r₀) , transport-is-equiv a)) (free-right-endpt-is-Contr A a₀)


--   iv-to-i : iv → i
--   iv-to-i ΣR-is-Contr D d = (curry (λ u → transport (Σ-induction D) (p u) d)) , (ap (λ - → transport (Σ-induction D) - d) q) where
--     p : (u : Σ R) → (a₀ , r₀) ≡ u
--     p = pr₂ (pr₁ isContr-iff-is-inhabited-Prop ΣR-is-Contr) (a₀ , r₀)
--     q : p (a₀ , r₀) ≡ refl (a₀ , r₀)
--     q = pr₂ (pr₁ isContr-iff-is-inhabited-Prop (pr₁ (Prop-iff-Contr-≡ (Σ R)) (pr₂ (pr₁ isContr-iff-is-inhabited-Prop ΣR-is-Contr)) (a₀ , r₀) (a₀ , r₀))) _ _ 


-- -- Definition 5.8.3 (identity system)

-- is-id-system : {A : 𝓤 ̇} → (Σ R ꞉ (A → A → 𝓤 ̇) , ((a : A) → R a a)) → 𝓤 ⁺ ̇
-- is-id-system {𝓤} {A} (R , r₀) = (D : (a b : A) → R a b → 𝓤 ̇) (d : (a : A) → D a a (r₀ a)) → Σ f ꞉ ((a b : A) (r : R a b) → D a b r) , ((a : A) → f a a (r₀ a) ≡ d a)


-- -- Theorem 5.8.4. (Fundamental theorem of identity types).

-- module thm-5-8-4 ⦃ fe : FunExt ⦄ (A : 𝓤 ̇) (R' : (Σ R ꞉ (A → A → 𝓤 ̇) , ((a : A) → R a a))) where

--   -- Unfold R'

--   R = pr₁ R'
--   r₀ = pr₂ R'

--   -- TFAE

--   i = is-id-system R'
--   ii = (a₀ : A) → is-based-id-system (R a₀ , r₀ a₀)
--   iii = (S' : (Σ R ꞉ (A → A → 𝓤 ̇) , ((a : A) → R a a))) → isContr (Σ g ꞉ ((a b : A) → R a b → pr₁ S' a b) , ((a : A) → g a a (r₀ a) ≡ pr₂ S' a))
--   iv = (a b : A) → isequiv (λ (p : a ≡ b) → transport (R a) p (r₀ a))
--   v = (a : A) → isContr (Σ b ꞉ A , R a b)

--   -- Proof of the logical equivalences

--   i-to-ii : i → ii
--   i-to-ii R'-is-id-system = {!!}


-- PROBLEM: WE NEED MULTIPLE UNIVERSES IN ORDER TO PROVE ii → i. 

  
-- Definition 5.8.1 (Pointed predicate, pointed family of maps, based identity system).

pted-pred : 𝓤 ⊙ → (𝓥 : Universe) → 𝓤 ⊔ 𝓥 ⁺ ̇
pted-pred {𝓤} (A , a₀) 𝓥 = Σ R ꞉ (A → 𝓥 ̇) , R a₀

ppmap : (A : 𝓤 ⊙) → pted-pred A 𝓥 → pted-pred A 𝓦 → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ̇
ppmap (A , a₀) (R , r₀) (S , s₀) = Σ g ꞉ Π (λ a → R a → S a) , g a₀ r₀ ≡ s₀ 

is-based-id-system : {A : 𝓤 ⊙} → pted-pred A 𝓥 → (𝓦 : Universe) → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ⁺ ̇ 
is-based-id-system {𝓤} {𝓥} {A , a₀} (R , r₀) 𝓦 = (D : (a : A) → R a → 𝓦 ̇) (d : D a₀ r₀) → Σ f ꞉ ((a : A) (r : R a) → D a r) , f a₀ r₀ ≡ d


-- Composition of pointed families of maps

ppmap-comp : (A : 𝓤 ⊙) (R : pted-pred A 𝓥) (S : pted-pred A 𝓦) (T : pted-pred A 𝓣) → ppmap A R S → ppmap A S T → ppmap A R T
ppmap-comp (A , a₀) (R , r₀) (S , s₀) (T , t₀) (f , fr) (g , gr) = (λ a → g a ∘ f a) , (ap (g a₀) fr ∙ gr)


-- Identity pointed familiy of maps

ppmap-id : (A : 𝓤 ⊙) (R : pted-pred A 𝓥) → ppmap A R R
ppmap-id (A , a₀) (R , r₀) = (λ a → id) , (refl r₀)


-- Identity type of pointed families of maps

ppmap-≡ : ⦃ fe : FunExt ⦄ (A : 𝓤 ⊙) (R : pted-pred A 𝓥) (S : pted-pred A 𝓦) (g h : ppmap A R S) → (g ≡ h) ≃ (Σ α ꞉ ((a : pr₁ A) (r : pr₁ R a) → pr₁ g a r ≡ pr₁ h a r) , (α (pr₂ A) (pr₂ R) ⁻¹ ∙ pr₂ g ≡ pr₂ h))
ppmap-≡ (A , a₀) (R , r₀) (S , s₀) (g , gr) (h , hr) = Σ-≡-equiv ● Σ-preserves-≃ _ _ ((happly , happly-is-equiv) ● Π-preserves-family-≃ (λ a → happly , happly-is-equiv)) λ p → (path p gr ⁻¹ ∙_ ) , (qinv-to-isequiv (qinv-pre-∙ hr (path p gr ⁻¹))) where
   path : {g h : Π λ a → R a → S a} (p : g ≡ h) (gr : g a₀ r₀ ≡ s₀) → transport (λ - → (- a₀ r₀) ≡ s₀) p gr ≡ happly (happly p a₀) r₀ ⁻¹ ∙ gr  
   path (refl _) gr = lu _


-- Theorem 5.8.2 (Fundamental theorem of based identity types).

module thm-5-8-2 ⦃ fe : FunExt ⦄ (A' : 𝓤 ⊙) (R' : pted-pred A' 𝓥) (𝓦 : Universe) where

  -- Unfold the pointed type and predicate

  A = pr₁ A'
  a₀ = pr₂ A'
  R = pr₁ R'
  r₀ = pr₂ R'

  -- TFAE

  i = is-based-id-system R' 𝓦
  ii = (S' : pted-pred A' 𝓦) → isContr (ppmap A' R' S')
  iii = (a : A) → isequiv (λ (- : a₀ ≡ a) → transport R - r₀)
  iv = isContr (Σ R)

  -- The statements are propositions (the proof of i-is-Prop is omitted).

  ii-is-Prop : isProp ii
  ii-is-Prop = Π-preserves-Props _ (λ S' → isContr-is-Prop _)

  iii-is-Prop : isProp iii
  iii-is-Prop = Π-preserves-Props _ (λ a → ishae-is-Prop _)

  iv-is-Prop : isProp iv
  iv-is-Prop = isContr-is-Prop _

  -- Proof of the logical equivalences.

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

-- Problem : we need initiality in multiple universes which, moreover, don't correspond to 𝓦 (𝓤 for the identity pted. predicate and 𝓥, for R). Do we need to lift everything to a common universe? Or should we use stronger statements (e.g. based path induction and initiality in all universes)?  

  -- ii-to-iii : ii → iii
  -- ii-to-iii R'-is-initial = λ a → qinv-to-isequiv (pr₁ inv-ppmap a , α' a , β' a)
  --   where

  --   -- Identity is a pointed predicate
    
  --   S : A → 𝓤 ̇
  --   S a = a₀ ≡ a
  --   s₀ : S a₀
  --   s₀ = refl a₀
  --   S' : pted-pred A' 𝓤
  --   S' = (S , s₀)

  --   -- Inverse pointed family of maps

  --   Contr₁ : isContr (ppmap A' R' S')
  --   Contr₁ = R'-is-initial S'
  --   inv-ppmap : ppmap A' R' S' 
  --   inv-ppmap = pr₁ Contr₁

  --   -- Right-invertibility

  --   Contr₂ : isContr (ppmap A' R' R')
  --   Contr₂ = R'-is-initial R'
  --   α : ppmap-comp A' R' S' R' inv-ppmap ((λ a p → transport R p r₀) , refl r₀) ≡ ppmap-id A' R'
  --   α = pr₂ (pr₁ isContr-iff-is-inhabited-Prop Contr₂) _ _
  --   α' : (a : A) (r : R a) → transport R (pr₁ inv-ppmap a r) r₀ ≡ r
  --   α' = pr₁ (pr₁ (ppmap-≡ A' R' R' (ppmap-comp A' R' S' R' inv-ppmap ((λ a p → transport R p r₀) , refl r₀)) (ppmap-id A' R')) α)

  --   -- Left-invertibility

  --   Contr₃ : isContr (ppmap A' S' S')
  --   Contr₃ = ppmap-id A' S' , Σ-induction (λ f fr → inv (ppmap-≡ A' S' S' (ppmap-id A' S') (f , fr)) ((ℍ a₀ (λ a p → pr₁ (ppmap-id A' S') a p ≡ f a p) (fr ⁻¹)) , (ru _ ⁻¹ ∙ ⁻¹-invol _)))
  --   β : ppmap-comp A' S' R' S' ((λ a p → transport R p r₀) , refl r₀) inv-ppmap ≡ ppmap-id A' S'
  --   β = pr₂ Contr₃ _ ⁻¹
  --   β' : (a : A) (p : S a) → pr₁ inv-ppmap a (transport R p r₀) ≡ p
  --   β' = pr₁ (pr₁ (ppmap-≡ A' S' S' (ppmap-comp A' S' R' S' ((λ a p → transport R p r₀) , refl r₀) inv-ppmap) (ppmap-id A' S')) β)
    

  iii-to-iv : iii → iv
  iii-to-iv transport-is-equiv = ≃-preserves-Contr (Σ-preserves-family-≃ (λ a → (λ (p : a₀ ≡ a) → transport R p r₀) , transport-is-equiv a)) (free-right-endpt-is-Contr A a₀)


  iv-to-i : iv → i
  iv-to-i ΣR-is-Contr D d = (curry (λ u → transport (Σ-induction D) (p u) d)) , (ap (λ - → transport (Σ-induction D) - d) q) where
    p : (u : Σ R) → (a₀ , r₀) ≡ u
    p = pr₂ (pr₁ isContr-iff-is-inhabited-Prop ΣR-is-Contr) (a₀ , r₀)
    q : p (a₀ , r₀) ≡ refl (a₀ , r₀)
    q = pr₂ (pr₁ isContr-iff-is-inhabited-Prop (pr₁ (Prop-iff-Contr-≡ (Σ R)) (pr₂ (pr₁ isContr-iff-is-inhabited-Prop ΣR-is-Contr)) (a₀ , r₀) (a₀ , r₀))) _ _ 



  
  





{-# OPTIONS --without-K --exact-split #-}

open import Ch1.Type-theory
open import Ch2.Homotopy-type-theory
open import Ch3.Sets-and-logic
open import Ch4.9-Univalence-implies-funext
open import Ch4.Exercises

module Ch4.1-Quasi-inverses ⦃ pt : PropTrunc ⦄ where


-- Lemma 4.1.1 (If f is quasi-invertible, then qinv f ≃ (id ∼ id)

inhabited-qinv-is-𝑖𝑑∼𝑖𝑑' : {A B : 𝓤 ̇} (p : A ≡ B) → qinv (pr₁ (idtoeqv p)) ≃ (𝑖𝑑 A ∼ 𝑖𝑑 A)
inhabited-qinv-is-𝑖𝑑∼𝑖𝑑' {𝓤} {A} {.A} (refl .A) =
  qinv (𝑖𝑑 A)
    ≃⟨ Σ-preserves-family-≃ (λ g → ×-preserves-≃ (≃-sym (happly , happly-is-equiv)) (≃-sym (happly , happly-is-equiv))) ⟩
  (Σ g ꞉ (A → A) , (g ≡ 𝑖𝑑 A) × (g ≡ 𝑖𝑑 A))
    ≃⟨ Σ-assoc _ _ _ ⟩
  (Σ h ꞉ (Σ g ꞉ (A → A) , g ≡ 𝑖𝑑 A) , pr₁ h ≡ 𝑖𝑑 A)
    ≃⟨ Σ-over-Contr-base-is-fib _ _ (free-left-endpt-is-Contr _ _) ⟩
  (𝑖𝑑 A ≡ 𝑖𝑑 A)
    ≃⟨ happly , happly-is-equiv ⟩
  (𝑖𝑑 A ∼ 𝑖𝑑 A) ■

inhabited-qinv-is-𝑖𝑑∼𝑖𝑑 : {A B : 𝓤 ̇} (f : A → B) → qinv f → qinv f ≃ (𝑖𝑑 A ∼ 𝑖𝑑 A)
inhabited-qinv-is-𝑖𝑑∼𝑖𝑑 {𝓤} {A} {B} f q =
  let e : isequiv f
      e = qinv-to-isequiv q
      p = A ≡ B
      p = ua (f , e)
  in qinv f
       ≃⟨ idtoeqv (ap (qinv ∘ pr₁) (idtoeqv-β' (f , e) ⁻¹)) ⟩
     qinv (pr₁ (idtoeqv (ua (f , qinv-to-isequiv q))))
       ≃⟨ inhabited-qinv-is-𝑖𝑑∼𝑖𝑑' p ⟩
     (𝑖𝑑 A ∼ 𝑖𝑑 A) ■


-- Lemma 4.1.2 (Sufficient conditions for non-trivial inhabitant of 𝑖𝑑 A ∼ 𝑖𝑑 A).

module nontrivial-inhabitant-criterion (A : 𝓤 ̇) (a : A) (q : a ≡ a) (i : isSet (a ≡ a)) (g : ((x : A) → ∥ a ≡ x ∥₋₁)) (comm : (p : a ≡ a) → p ∙ q ≡ q ∙ p) where

  first : is-⟨1⟩-type A
  first x y = ∥∥₋₁-recursion (isSet-is-Prop (x ≡ y)) (λ p' → ∥∥₋₁-recursion (isSet-is-Prop (x ≡ y)) (λ p → ≃-preserves-Sets (≃-sym ((λ r → p ∙ r ∙ p' ⁻¹) , aux-equiv p p')) i) (g x)) (g y) where    
    aux-equiv : (p : a ≡ x) (p' : a ≡ y) → isequiv (λ r → p ∙ r ∙ p' ⁻¹)
    aux-equiv p p' = qinv-to-isequiv (
      (λ s → p ⁻¹  ∙ s ∙ p') ,
      (λ s → (∙-assoc _ _ _ ∙ᵣ p' ⁻¹) ∙ (ap (λ - → - ∙ p' ∙ p' ⁻¹) (∙-assoc _ _ _ ∙ (rinv p ∙ᵣ s) ∙ lu s ⁻¹) ∙ (∙-assoc _ _ _ ⁻¹ ∙ (s ∙ₗ rinv p') ∙ ru s ⁻¹  ))) , 
      λ r → ap (λ - → p ⁻¹ ∙ - ∙ p') (∙-assoc _ _ _ ⁻¹) ∙ ((∙-assoc _ _ _ ∙ᵣ p') ∙ (ap (λ - → - ∙ (r ∙ p' ⁻¹) ∙ p') (linv p) ∙ (lu _ ⁻¹ ∙ᵣ p') ∙ ∙-assoc _ _ _ ⁻¹ ∙ (r ∙ₗ linv p') ∙ ru _ ⁻¹ )) 
      )

  B : A → 𝓤 ̇
  B x = Σ r ꞉ (x ≡ x) , ((s : a ≡ x) → r ≡ s ⁻¹ ∙ (q ∙ s))

  second : (x : A) → isProp (B x)
  second x = ∥∥₋₁-recursion (isProp-is-Prop (B x)) (λ p → Σ-induction λ r h → Σ-induction λ r' h' → dpair-≡ ((h p ∙ h' p ⁻¹) , funext (λ s → first x x _ _ _ _))) (g x)

  third : Π B
  third x = ∥∥₋₁-recursion (second x) (λ p → (p ⁻¹ ∙ (q ∙ p)) , λ s → ((ap (λ - → (p ⁻¹) ∙ -) (ru _ ∙ (ap (λ - → (q ∙ p) ∙ - ) (linv s ⁻¹) ∙ (∙-assoc _ _ _ ∙ ((ap (λ - → - ∙ s) ((∙-assoc _ _ _ ⁻¹) ∙ (comm (p ∙ (s ⁻¹)) ⁻¹)) ∙ (∙-assoc _ _ _ ⁻¹)) ∙ (∙-assoc _ _ _ ⁻¹))))) ∙ (∙-assoc _ _ _)) ∙ ap (λ - → - ∙ ((s ⁻¹) ∙ (q ∙ s))) (linv p)) ∙ (lu _ ⁻¹)) (g x)

  nontrivial-inhabitant-criterion : Σ f ꞉ (𝑖𝑑 A ∼ 𝑖𝑑 A) , f a ≡ q
  nontrivial-inhabitant-criterion = (λ x → pr₁ (third x)) , (pr₂ (third a) (refl a) ∙ lu _ ⁻¹ ∙ ru _ ⁻¹)


-- Theorem 4.1.3

module qinv-is-not-Prop where

  X : 𝓤₀ ⁺ ̇
  X = Σ A ꞉ (𝓤₀ ̇) , ∥ 𝟚 ≡ A ∥₋₁

  X-≡ : {x y : X} → (x ≡ y) ≃ (pr₁ x ≡ pr₁ y)
  X-≡ {x} {y} = Σ-over-predicate' (λ A → ∥∥₋₁-is-Prop) x y
  
  X-≡-η : {x y : X} → inv X-≡ ∘ pr₁ X-≡ ∼ 𝑖𝑑 (x ≡ y) 
  X-≡-η {x} {y} = isequiv₂ (pr₂ (X-≡ {x} {y}))

  X-≡-β : {x y : X} → pr₁ X-≡ ∘ inv X-≡ ∼ 𝑖𝑑 (pr₁ x ≡ pr₁ y)
  X-≡-β {x} {y} = isequiv₃ (pr₂ (X-≡ {x} {y}))

  a : X
  a = 𝟚 , ∣ refl 𝟚 ∣₋₁

  q : a ≡ a
  q = inv X-≡ (ua twist-≃) 

  i : isSet (a ≡ a)
  i = ≃-preserves-Sets (≃-sym (X-≡ ● idtoeqv , idtoeqv-is-equiv ● autoequivs-of-𝟚)) 𝟚-is-Set

  g : (x : X) → ∥ a ≡ x ∥₋₁
  g (A , p) = ∥∥₋₁-recursion ∥∥₋₁-is-Prop (∣_∣₋₁ ∘ inv X-≡) p

  𝟚-path-classification : (p : 𝟚 ≡ 𝟚) → (p ≡ refl 𝟚) + (p ≡ ua twist-≃)
  𝟚-path-classification p =
    +-recursion
      (λ path → inl (idtoeqv-η p ⁻¹ ∙ (ap ua path ∙ type-refl 𝟚 ⁻¹)))
      (λ path → inr (idtoeqv-η p ⁻¹ ∙ ap ua path))
      (𝟚-autoequiv-classification (idtoeqv p))

  uatwist-is-not-refl : ¬ (ua twist-≃ ≡ refl 𝟚)
  uatwist-is-not-refl p = twist-≃-is-not-≃-refl (idtoeqv-β' _ ⁻¹ ∙ ap idtoeqv (p ∙ type-refl 𝟚) ∙ idtoeqv-β' _)

  a-path-classification : (p : a ≡ a) → (p ≡ refl a) + (p ≡ q)
  a-path-classification p =
    +-recursion
      (λ path → inl (X-≡-η p ⁻¹ ∙ ap (inv X-≡) path ∙ X-≡-η (refl a)))
      (λ path → inr (X-≡-η p ⁻¹ ∙ ap (inv X-≡) path))
      (𝟚-path-classification (pr₁ X-≡ p))
      
  q-is-not-refl-a : ¬ (q ≡ refl a)
  q-is-not-refl-a path = uatwist-is-not-refl (X-≡-β _ ⁻¹ ∙ ap (pr₁ X-≡) (path ∙ X-≡-η (refl a) ⁻¹) ∙ X-≡-β _)
  
  comm : (p : a ≡ a) → p ∙ q ≡ q ∙ p
  comm p =
    +-recursion
      (λ path → (path ∙ᵣ q) ∙ (lu q ⁻¹ ∙ (ru q ∙ (q ∙ₗ path ⁻¹))))
      (λ path → (path ∙ᵣ q) ∙ (q ∙ₗ path ⁻¹))
      (a-path-classification p)

  open nontrivial-inhabitant-criterion {𝓤₀ ⁺} X a q i g comm

  f : 𝑖𝑑 X ∼ 𝑖𝑑 X 
  f = pr₁ nontrivial-inhabitant-criterion
  path : f a ≡ q
  path = pr₂ nontrivial-inhabitant-criterion

  𝑖𝑑∼𝑖𝑑-is-not-Prop : ¬ (isProp (𝑖𝑑 X ∼ 𝑖𝑑 X))
  𝑖𝑑∼𝑖𝑑-is-not-Prop w = q-is-not-refl-a ((happly (w (hrefl _) f) a ∙ path) ⁻¹)
   
  qinv-is-not-Prop : ¬ (isProp (qinv (𝑖𝑑 X)))
  qinv-is-not-Prop p = 𝑖𝑑∼𝑖𝑑-is-not-Prop (≃-preserves-Props (inhabited-qinv-is-𝑖𝑑∼𝑖𝑑 {𝓤₀ ⁺} {X} {X} id (qinv-𝑖𝑑 X)) p)

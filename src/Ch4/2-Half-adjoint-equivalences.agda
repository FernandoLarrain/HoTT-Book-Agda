{-# OPTIONS --without-K --exact-split --safe #-}

open import Ch1.Type-theory
open import Ch2.Homotopy-type-theory
open import Ch3.Sets-and-logic

module Ch4.2-Half-adjoint-equivalences where


-- Definition 4.2.1 (Half adjoint equivalence)

ishae : {A : 𝓤 ̇} {B : 𝓥 ̇} (f : A → B) → 𝓤 ⊔ 𝓥 ̇
ishae {A = A} {B} f = Σ g ꞉ (B → A) , Σ η ꞉ g ∘ f ∼ id , Σ ε ꞉ f ∘ g ∼ id , ((x : A) → ap f (η x) ≡ ε (f x))

ishae₁ : {A : 𝓤 ̇} {B : 𝓥 ̇} {f : A → B} → ishae f → B → A
ishae₁ (g , η , ε , τ) = g

ishae₂ : {A : 𝓤 ̇} {B : 𝓥 ̇} {f : A → B} → (h : ishae f) → ishae₁ h ∘ f ∼ id
ishae₂ (g , η , ε , τ) = η

ishae₃ : {A : 𝓤 ̇} {B : 𝓥 ̇} {f : A → B} → (h : ishae f) → f ∘ ishae₁ h ∼ id
ishae₃ (g , η , ε , τ) = ε

ishae₄ : {A : 𝓤 ̇} {B : 𝓥 ̇} {f : A → B} → (h : ishae f) → (x : A) → ap f (ishae₂ h x) ≡ ishae₃ h (f x)
ishae₄ (g , η , ε , τ) = τ

ishae' : {A : 𝓤 ̇} {B : 𝓥 ̇} (f : A → B) → 𝓤 ⊔ 𝓥 ̇
ishae' {A = A} {B} f = Σ g ꞉ (B → A) , Σ η ꞉ g ∘ f ∼ id , Σ ε ꞉ f ∘ g ∼ id , ((y : B) → ap g (ε y) ≡ η (g y))


-- Lemma 4.2.2 (Coherence conditions of ishae and ishae' are logically equivalent).

ishae-iff-ishae' : {A : 𝓤 ̇} {B : 𝓥 ̇} (f : A → B) (g : B → A) (η : g ∘ f ∼ id) (ε : f ∘ g ∼ id) → (((x : A) → ap f (η x) ≡ ε (f x)) → ((y : B) → ap g (ε y) ≡ η (g y))) × (((y : B) → ap g (ε y) ≡ η (g y)) → ((x : A) → ap f (η x) ≡ ε (f x))) 
ishae-iff-ishae' {A = A} {B} f g η ε = sufficiency , necessity where

  sufficiency : ((x : A) → ap f (η x) ≡ ε (f x)) → ((y : B) → ap g (ε y) ≡ η (g y))
  sufficiency τ y rewrite
    apd (λ - → ap g (ε -)) (ε y) ⁻¹ |  
    transport-funval-≡ (g ∘ (f ∘ g)) g (ε y) (ap g (ε ((f ∘ g) y))) |
    τ (g y) ⁻¹ |
    ap-∘ f g (η (g y)) |
    hnat-id η (g y) ⁻¹ |
    ap-id (ap g (ε y)) ⁻¹ |
    ap-∘ g (g ∘ f) (ε y) ⁻¹ |
    hnat'' η (ap g (ε y))
    = refl _  
        
  necessity : ((y : B) → ap g (ε y) ≡ η (g y)) → ((x : A) → ap f (η x) ≡ ε (f x))
  necessity ν x rewrite
    apd (λ - → ap f (η -)) (η x) ⁻¹ |
    transport-funval-≡ (f ∘ (g ∘ f)) f (η x) (ap f (η ((g ∘ f) x))) |
    ν (f x) ⁻¹ |
    ap-∘ g f (ε (f x)) |
    hnat-id ε (f x) ⁻¹ |
    ap-id (ap f (η x)) ⁻¹ |
    ap-∘ f (f ∘ g) (η x) ⁻¹ |
    hnat'' ε (ap f (η x))
    = refl _


-- Theorem 4.2.3 (Quasi-invertible maps are half-adjoint equivalences).

qinv-to-ishae : {A : 𝓤 ̇} {B : 𝓥 ̇} {f : A → B} → qinv f → ishae f
qinv-to-ishae {A = A} {f = f} (g , ε , η) =
  g ,
  η ,
  (λ b → ε (f (g b)) ⁻¹ ∙ ap f (η (g b)) ∙ ε b) ,
  τ
  where
  τ : (x : A) → ap f (η x) ≡ ε (f (g (f x))) ⁻¹ ∙ ap f (η (g (f x))) ∙ ε (f x)
  τ x rewrite
    hnat-id η x |
    ap-∘ (g ∘ f) f (η x) |
    ap-∘ f (f ∘ g) (η x) ⁻¹ |
    hnat' ε (ap f (η x)) |
    ap-id (ap f (η x)) 
    = refl _

-- Definition of τ without rewrite:
-- λ x → (
--     ap (λ - → ε (f (g (f x))) ⁻¹ ∙ ap f - ∙ ε (f x)) (hnat-id η x) ∙
--     ap (λ - → ε (f (g (f x))) ⁻¹ ∙ - ∙ ε (f x)) (ap-∘ (g ∘ f) _ (η x) ∙ (ap-∘ f (f ∘ g) (η x) ⁻¹)) ∙
--     hnat' ε (ap f (η x)) ∙
--     ap-id _
--     ) ⁻¹

ishae-to-qinv : {A : 𝓤 ̇} {B : 𝓥 ̇} {f : A → B} → ishae f → qinv f
ishae-to-qinv (g , η , ε , τ) = (g , ε , η)


-- Definition 4.2.4 (Fiber).

fib : {A : 𝓤 ̇} {B : 𝓥 ̇} (f : A → B) → B → 𝓤 ⊔ 𝓥 ̇
fib {𝓤} {𝓥} {A} {B} f y = Σ x ꞉ A , (f x ≡ y)


-- Lemma 4.2.5 (Path space of fibers).

path-space-fib : {A : 𝓤 ̇} {B : 𝓥 ̇} {f : A → B} {y : B} → (w w' : fib f y) → (w ≡ w') ≃ (Σ γ ꞉ (pr₁ w ≡ pr₁ w') , (ap f γ ∙ pr₂ w' ≡ pr₂ w))
path-space-fib {A = A} {f = f} {y} (x , p) (x' , p') =
  Σ-≡-equiv ●
  Σ-preserves-family-≃ (
    λ γ → ((λ r → bpi x' γ ⁻¹ ∙ r) , (qinv-to-isequiv (qinv-pre-∙ _ (bpi x' γ ⁻¹)))) ●
    (ap f γ ∙ₗ_) , qinv-to-isequiv (qinv-∙ₗ _ _ _) ●
    (λ x₁ → lu _ ∙ ap (_∙ p) (rinv _ ⁻¹) ∙ ∙-assoc _ _ _ ⁻¹ ∙ x₁) , (qinv-to-isequiv (qinv-pre-∙ _ _)) ●
    _⁻¹ , (qinv-to-isequiv (qinv-⁻¹ p (ap f γ ∙ p')))
  )
  where
  bpi : (x' : A) (γ : x ≡ x') → transport (λ x₁ → f x₁ ≡ y) γ p ≡ (ap f γ ⁻¹ ∙ p)
  bpi x' (refl .x') = lu _ -- maybe we can just use transport-funval-≡ with a constant function
  -- bpi stands for based path-induction. Change name!

-- Theorem 4.2.6 (Haes are contractible maps (see Def. 4.1.1 in Ch4.4-Contractible-fibers)).

ishae-to-isContrMap : {A : 𝓤 ̇} {B : 𝓥 ̇} (f : A → B) → ishae f → (y : B) → isContr (fib f y)
ishae-to-isContrMap f (g , η , ε , τ) y =
  ((g y) , (ε y)) ,
  Σ-induction {A = λ (w : fib f y) → g y , ε y ≡ w} λ x p → isequiv₁ (pr₂ (path-space-fib (g y , ε y) (x , p))) (
    (ap g p ⁻¹ ∙ η x) ,
    (ap (_∙ p) (ap-∙ f (ap g p ⁻¹) (η x)) ∙
    ap (λ - → ap f (ap g p ⁻¹) ∙ - ∙ p) (τ x) ∙
    ap (λ - → - ∙ ε (f x) ∙ p) (ap-⁻¹ f (ap g p) ∙ ap _⁻¹ (ap-∘ g f p)) ∙
    ap (ap (f ∘ g) p ⁻¹ ∙ ε (f x) ∙_) (ap-id p ⁻¹) ∙
    hnat'' ε p)
  )


-- Definition 4.2.7 (left- and right-invertible maps)

has-linv : {A : 𝓤 ̇} {B : 𝓥 ̇} → (A → B) → 𝓤 ⊔ 𝓥 ̇   
has-linv {A = A} {B} f = Σ g ꞉ (B → A) , g ∘ f ∼ 𝑖𝑑 A

has-rinv : {A : 𝓤 ̇} {B : 𝓥 ̇} → (A → B) → 𝓤 ⊔ 𝓥 ̇   
has-rinv {A = A} {B} f = Σ g ꞉ (B → A) , f ∘ g ∼ 𝑖𝑑 B

{- has-rinv and has-section are definitionally the same and can be used interchangeably. -}


-- Lemma 4.2.8: Copied to Ch2.Exercises. It is useful in problem 2.17 and does not require later results.


-- Lemma 4.2.9 (Invertibility data of quasi-invertible maps is contractible).

module _ ⦃ fe : FunExt ⦄ where 

  has-rinv-of-qinv-is-Contr : {A : 𝓤 ̇} {B : 𝓥 ̇} (f : A → B) → qinv f → isContr (has-rinv f)  
  has-rinv-of-qinv-is-Contr {A = A} {B} f q = retract-of-Contr-is-Contr (≃-to-◁ by-funext) (fiber-of-post-∘-is-Contr id)
    where
    by-funext : fib (λ g → f ∘ g) id ≃ has-rinv f
    by-funext = Σ-preserves-family-≃ (λ g → happly , happly-is-equiv)
    fiber-of-post-∘-is-Contr : (h : B → B) → isContr (fib (λ g → f ∘ g) h)
    fiber-of-post-∘-is-Contr = ishae-to-isContrMap (λ g → f ∘ g) (qinv-to-ishae (post-∘-by-qinv-is-qinv B f q))  

  has-linv-of-qinv-is-Contr : {A : 𝓤 ̇} {B : 𝓥 ̇} (f : A → B) → qinv f → isContr (has-linv f)  
  has-linv-of-qinv-is-Contr {A = A} {B} f q = retract-of-Contr-is-Contr (≃-to-◁ by-funext) (fiber-of-post-∘-is-Contr id)
    where
    by-funext : fib (λ g → g ∘ f) id ≃ has-linv f
    by-funext = Σ-preserves-family-≃ (λ g → happly , happly-is-equiv)
    fiber-of-post-∘-is-Contr : (h : A → A) → isContr (fib (λ g → g ∘ f) h)
    fiber-of-post-∘-is-Contr = ishae-to-isContrMap (λ g → g ∘ f) (qinv-to-ishae (pre-∘-by-qinv-is-qinv A f q))


-- Definition 4.2.10 (Coherence data)

lcoh : {A : 𝓤 ̇} {B : 𝓥 ̇} (f : A → B) → has-linv f → 𝓤 ⊔ 𝓥 ̇ 
lcoh {B = B} f (g , η) = Σ ε ꞉ (f ∘ g ∼ id) , ((y : B) → ap g (ε y) ≡ η (g y))

rcoh : {A : 𝓤 ̇} {B : 𝓥 ̇} (f : A → B) → has-rinv f → 𝓤 ⊔ 𝓥 ̇ 
rcoh {A = A} f (g , ε) = Σ η ꞉ (g ∘ f ∼ id) , ((x : A) → ap f (η x) ≡ ε (f x))


-- Lemma 4.2.11 (Characterization of coherence data in terms of fibers).

module coh-≃-fib {A : 𝓤 ̇} {B : 𝓥 ̇} (f : A → B) where

  fib-to-rcoh : (r : has-rinv f) → ((x : A) → Id (fib f (f x)) (pr₁ r (f x) , pr₂ r (f x)) (x , refl (f x))) →  rcoh f r
  fib-to-rcoh (g , ε) h = (λ x → pr₁ (k x)) , (λ x → ru _ ∙ pr₂ (k x))
    where
    k : (x : A) → Σ p ꞉ g (f x) ≡ x , (ap f p ∙ refl (f x) ≡ ε (f x))
    k = λ x → pr₁ (path-space-fib _ _) (h x)

  module _ ⦃ fe : FunExt ⦄ where  

    lcoh-≃-fib : (l : has-linv f) → lcoh f l ≃ ((y : B) → Id (fib (pr₁ l) (pr₁ l y)) (f (pr₁ l y) , pr₂ l (pr₁ l y)) (y , refl (pr₁ l y)))
    lcoh-≃-fib (g , η) = ≃-sym (Π-preserves-family-≃ by-path-space-fib ● choice-fun , dep-Σ-UMP _ _ _)
      where  
      by-path-space-fib : (y : B) → (Id (fib g (g y)) (f (g y) , η (g y)) (y , refl (g y))) ≃ (Σ γ ꞉ (f (g y) ≡ y) , (ap g (γ) ≡ η (g y))) 
      by-path-space-fib y = path-space-fib (f (g y) , η (g y)) (y , refl (g y)) ● Σ-preserves-family-≃ (λ γ → (ru (ap g γ) ∙_) , (qinv-to-isequiv (qinv-pre-∙ _ _))) 
      choice-fun : Π (λ y → Σ λ γ → ap g γ ≡ η (g y)) → Σ (λ Γ → Π (λ y → ap g (Γ y) ≡ η (g y)))  
      choice-fun = λ F → (λ y → pr₁ (F y)) , λ y → pr₂ (F y)

    rcoh-≃-fib : (r : has-rinv f) → rcoh f r ≃ ((x : A) → Id (fib f (f x)) (pr₁ r (f x) , pr₂ r (f x)) (x , refl (f x)))
    rcoh-≃-fib (g , ε) = ≃-sym (Π-preserves-family-≃ by-path-space-fib ● choice-fun , dep-Σ-UMP _ _ _)
      where  
      by-path-space-fib : (x : A) → (Id (fib f (f x)) (g (f x) , ε (f x)) (x , refl (f x))) ≃ (Σ γ ꞉ (g (f x) ≡ x) , (ap f (γ) ≡ ε (f x))) 
      by-path-space-fib x = path-space-fib (g (f x) , ε (f x)) (x , refl (f x)) ● Σ-preserves-family-≃ (λ γ → (ru (ap f γ) ∙_) , (qinv-to-isequiv (qinv-pre-∙ _ _))) 
      choice-fun : Π (λ x → Σ λ γ → ap f γ ≡ ε (f x)) → Σ (λ Γ → Π (λ x → ap f (Γ x) ≡ ε (f x)))  
      choice-fun = λ F → (λ x → pr₁ (F x)) , λ x → pr₂ (F x)

open coh-≃-fib public 

module _ ⦃ fe : FunExt ⦄ where

  -- Lemma 4.2.12 (Right coherence-data of haes is contractible)

  rcoh-of-hae-is-Contr : {A : 𝓤 ̇} {B : 𝓥 ̇} (f : A → B) → ishae f → (r : has-rinv f) → isContr (rcoh f r)
  rcoh-of-hae-is-Contr f h (g , ε) = retract-of-Contr-is-Contr (≃-to-◁ (≃-sym (rcoh-≃-fib f (g , ε)))) (Π-preserves-Contr _ λ x → pr₁ (Prop-iff-Contr-≡ _) (pr₂ (pr₁ (isContr-iff-is-inhabited-Prop (fib f (f x))) (ishae-to-isContrMap f h (f x)))) _ _)


  -- Theorem 4.2.13 (ishae is a proposition).

  ishae-is-Prop : {A : 𝓤 ̇} {B : 𝓥 ̇} (f : A → B) → isProp (ishae f)
  ishae-is-Prop {A = A} {B} f = suffices λ h → retract-of-Contr-is-Contr (≃-to-◁ equivalence) (Σ-preserves-Contr _ _ (has-rinv-of-qinv-is-Contr f (ishae-to-qinv h)) (rcoh-of-hae-is-Contr f h))
    where
    suffices : (ishae f → isContr (ishae f)) → isProp (ishae f)
    suffices = inv (isProp-≃-inhabited→isContr (ishae f))
    equivalence : Σ (λ (u : has-rinv f) → rcoh f u) ≃ ishae f
    equivalence =
      Σ (λ (u : has-rinv f) → rcoh f u)
        ≃⟨ ≃-sym (Σ-assoc _ _ (λ (u : has-rinv f) → rcoh f u)) ⟩
      (Σ λ (g : B → A) → Σ λ (ε : f ∘ g ∼ id) → rcoh f (g , ε))
        ≃⟨ Σ-preserves-family-≃ (λ g → Σ-swap _ _ _) ⟩
      ishae f ■

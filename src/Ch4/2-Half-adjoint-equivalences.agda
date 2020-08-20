{-# OPTIONS --without-K --exact-split --safe #-}

open import Ch1.Type-theory
open import Ch2.Homotopy-type-theory
open import Ch3.Sets-and-logic

module Ch4.2-Half-adjoint-equivalences where


-- Definition 4.2.1 (Half adjoint equivalence)

ishae : {A : 𝓤 ̇} {B : 𝓥 ̇} (f : A → B) → 𝓤 ⊔ 𝓥 ̇
ishae {𝓤} {𝓥} {A} {B} f = Σ g ꞉ (B → A) , Σ η ꞉ g ∘ f ∼ id , Σ ε ꞉ f ∘ g ∼ id , ((x : A) → ap f (η x) ≡ ε (f x))

module ishae {A : 𝓤 ̇} {B : 𝓥 ̇} {f : A → B} where

  ishae₁ : ishae f → B → A
  ishae₁ (g , η , ε , τ) = g

  ishae₂ : (h : ishae f) → ishae₁ h ∘ f ∼ id
  ishae₂ (g , η , ε , τ) = η

  ishae₃ : (h : ishae f) → f ∘ ishae₁ h ∼ id
  ishae₃ (g , η , ε , τ) = ε

  ishae₄ : (h : ishae f) → (x : A) → ap f (ishae₂ h x) ≡ ishae₃ h (f x)
  ishae₄ (g , η , ε , τ) = τ

ishae' : {A : 𝓤 ̇} {B : 𝓥 ̇} (f : A → B) → 𝓤 ⊔ 𝓥 ̇
ishae' {𝓤} {𝓥} {A} {B} f = Σ g ꞉ (B → A) , Σ η ꞉ g ∘ f ∼ id , Σ ε ꞉ f ∘ g ∼ id , ((y : B) → ap g (ε y) ≡ η (g y))


-- Lemma 4.2.2 (Coherence conditions of ishae and ishae' are logically equivalent).

ishae-iff-ishae' : {A : 𝓤 ̇} {B : 𝓥 ̇} (f : A → B) (g : B → A) (η : g ∘ f ∼ id) (ε : f ∘ g ∼ id) → (((x : A) → ap f (η x) ≡ ε (f x)) ⇔ ((y : B) → ap g (ε y) ≡ η (g y)))
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
qinv-to-ishae {𝓤} {𝓥} {A} {B} {f} (g , ε , η) = g , η , ε' , τ
  where
  ε' : f ∘ g ∼ id
  ε' = (λ b → ε (f (g b)) ⁻¹ ∙ ap f (η (g b)) ∙ ε b)
  τ : (x : A) → ap f (η x) ≡ ε (f (g (f x))) ⁻¹ ∙ ap f (η (g (f x))) ∙ ε (f x)
  τ x rewrite
    hnat-id η x |
    ap-∘ (g ∘ f) f (η x) |
    ap-∘ f (f ∘ g) (η x) ⁻¹ |
    hnat' ε (ap f (η x)) |
    ap-id (ap f (η x)) 
    = refl _


-- "Forgetful" map from half-adjoint equivalences to quasi-inverses.

ishae-to-qinv : {A : 𝓤 ̇} {B : 𝓥 ̇} {f : A → B} → ishae f → qinv f
ishae-to-qinv (g , η , ε , τ) = (g , ε , η)


-- Definition 4.2.4 (Fiber).

fib : {A : 𝓤 ̇} {B : 𝓥 ̇} (f : A → B) → B → 𝓤 ⊔ 𝓥 ̇
fib {𝓤} {𝓥} {A} {B} f y = Σ x ꞉ A , (f x ≡ y)


-- Lemma 4.2.5 (Path space of fibers).

path-space-fib : {A : 𝓤 ̇} {B : 𝓥 ̇} {f : A → B} {y : B} → (w w' : fib f y) → (w ≡ w') ≃ (Σ γ ꞉ (pr₁ w ≡ pr₁ w') , (ap f γ ∙ pr₂ w' ≡ pr₂ w))
path-space-fib {𝓤} {𝓥} {A} {B} {f} {y} (x , p) (x' , p') = Σ-≡-≃ ● Σ-preserves-family-≃ family-≃ where
  family-≃ : (γ : x ≡ x') → (transport (λ - → f - ≡ y) γ p ≡ p') ≃ (ap f γ ∙ p' ≡ p)
  family-≃ γ =
    (transport (λ - → f - ≡ y) γ p ≡ p')
      ≃⟨ pre-∙-≃ _ (lhs-≡₁ ⁻¹) ⟩ 
    (ap f γ ⁻¹ ∙ p ≡ p')
      ≃⟨ ≃-sym (∙ₗ-≃ (ap f γ) _ _) ⟩
    (ap f γ ∙ (ap f γ ⁻¹ ∙ p) ≡ ap f γ ∙ p')
      ≃⟨ pre-∙-≃ _ lhs-≡₂ ⟩
    (p ≡ ap f γ ∙ p')
      ≃⟨ ⁻¹-≃ _ _ ⟩
    ((ap f γ ∙ p' ≡ p) ■)
    where
    lhs-≡₁ : transport (λ - → f - ≡ y) γ p ≡ ap f γ ⁻¹ ∙ p
    lhs-≡₁ = transport-funval-≡ f (λ a → y) γ p ∙ ap (ap f γ ⁻¹ ∙ p ∙_) (ap-const-fun y γ) ∙ ru _ ⁻¹
    lhs-≡₂ : p ≡ ap f γ ∙ (ap f γ ⁻¹ ∙ p)
    lhs-≡₂ = lu p ∙ ap (_∙ p) (rinv (ap f γ) ⁻¹) ∙ ∙-assoc _ _ _ ⁻¹


-- Path space of fiber f is fiber of ap f.

path-space-fib-is-fib-of-ap : {A : 𝓤 ̇} {B : 𝓥 ̇} {f : A → B} {y : B} → (w w' : fib f y) → (w ≡ w') ≃ fib (ap f {pr₁ w} {pr₁ w'}) (pr₂ w ∙ pr₂ w' ⁻¹)
path-space-fib-is-fib-of-ap {𝓤} {𝓥} {A} {B} {f} {y} (x , p) (x' , q) =
  ((x , p) ≡ (x' , q))
    ≃⟨ path-space-fib _ _ ⟩
  (Σ γ ꞉ x ≡ x' , (ap f γ ∙ q ≡ p))
    ≃⟨ Σ-preserves-family-≃ (λ γ → aux-equiv γ p q) ⟩
  fib (ap f {x} {x'}) (p ∙ q ⁻¹) ■
  where
  aux-equiv : {x x' : A} (γ : x ≡ x') {y : B} (p : f x ≡ y) (q : f x' ≡ y) → (ap f γ ∙ q ≡ p) ≃ (ap f γ ≡ p ∙ q ⁻¹)
  aux-equiv (refl _) p (refl .(f _)) = post-∙-≃ _ (ru p)


-- Fiber of ap f is path space of fiber f

fib-of-ap-is-path-space-fib :  {A : 𝓤 ̇} {B : 𝓥 ̇} {f : A → B} {x x' : A} (p : f x ≡ f x') → fib (ap f {x} {x'}) p ≃ ((x , p) ≡ (x' , refl (f x')))
fib-of-ap-is-path-space-fib {𝓤} {𝓥} {A} {B} {f} {x} {x'} p = ≃-sym (
  ((x , p) ≡ (x' , refl (f x')))
    ≃⟨ path-space-fib-is-fib-of-ap (x , p) (x' , refl (f x')) ⟩
  fib (ap f {x} {x'}) (p ∙ refl (f x'))
    ≃⟨ Σ-preserves-family-≃ (λ γ → post-∙-≃ _ (ru p ⁻¹)) ⟩
  fib (ap f {x} {x'}) p ■
  )


-- Theorem 4.2.6 (Haes are contractible maps (see Def. 4.1.1 in Ch4.4-Contractible-fibers)).

ishae-to-isContrMap : {A : 𝓤 ̇} {B : 𝓥 ̇} (f : A → B) → ishae f → (y : B) → isContr (fib f y)
ishae-to-isContrMap f (g , η , ε , τ) y =
  ((g y) , (ε y)) ,
  Σ-induction {A = λ (w : fib f y) → g y , ε y ≡ w} λ x p → inv (path-space-fib (g y , ε y) (x , p)) (
    (ap g p ⁻¹ ∙ η x) ,
    (ap (_∙ p) (ap-∙ f (ap g p ⁻¹) (η x)) ∙
    ap (λ - → ap f (ap g p ⁻¹) ∙ - ∙ p) (τ x) ∙
    ap (λ - → - ∙ ε (f x) ∙ p) (ap-⁻¹ f (ap g p) ∙ ap _⁻¹ (ap-∘ g f p)) ∙
    ap (ap (f ∘ g) p ⁻¹ ∙ ε (f x) ∙_) (ap-id p ⁻¹) ∙
    hnat'' ε p)
  )


-- Definition 4.2.7 (left- and right-invertible maps)

private

  has-linv : {A : 𝓤 ̇} {B : 𝓥 ̇} → (A → B) → 𝓤 ⊔ 𝓥 ̇   
  has-linv {𝓤} {𝓥} {A} {B} f = Σ g ꞉ (B → A) , g ∘ f ∼ 𝑖𝑑 A

  _ : {A : 𝓤 ̇} {B : 𝓥 ̇} (f : A → B) → has-linv f ≡ ret f
  _ = hrefl _

  has-rinv : {A : 𝓤 ̇} {B : 𝓥 ̇} → (A → B) → 𝓤 ⊔ 𝓥 ̇   
  has-rinv {A = A} {B} f = Σ g ꞉ (B → A) , f ∘ g ∼ 𝑖𝑑 B

  _ : {A : 𝓤 ̇} {B : 𝓥 ̇} (f : A → B) → has-rinv f ≡ sec f
  _ = hrefl _


-- Lemma 4.2.8: Copied to Ch2.Exercises. It is useful in problem 2.17 and does not require later results.


-- Lemma 4.2.9 (Invertibility data of quasi-invertible maps is contractible).

module _ ⦃ fe : FunExt ⦄ where 

  sec-of-qinv-is-Contr : {A : 𝓤 ̇} {B : 𝓥 ̇} (f : A → B) → qinv f → isContr (sec f)  
  sec-of-qinv-is-Contr {𝓤} {𝓥} {A} {B} f q = retract-of-Contr-is-Contr (≃-to-◁ by-funext) (fib-of-post-∘-is-Contr id)
  
    where
    
    by-funext : fib (λ g → f ∘ g) id ≃ sec f
    by-funext = Σ-preserves-family-≃ (λ g → happly , happly-is-equiv)
    fib-of-post-∘-is-Contr : (h : B → B) → isContr (fib (λ g → f ∘ g) h)
    
    fib-of-post-∘-is-Contr = ishae-to-isContrMap (λ g → f ∘ g) (qinv-to-ishae (post-∘-by-qinv-is-qinv B f q))  

  ret-of-qinv-is-Contr : {A : 𝓤 ̇} {B : 𝓥 ̇} (f : A → B) → qinv f → isContr (ret f)  
  ret-of-qinv-is-Contr {𝓤} {𝓥} {A} {B} f q = retract-of-Contr-is-Contr (≃-to-◁ by-funext) (fib-of-post-∘-is-Contr id)
  
    where
    
    by-funext : fib (λ g → g ∘ f) id ≃ ret f
    by-funext = Σ-preserves-family-≃ (λ g → happly , happly-is-equiv)
    
    fib-of-post-∘-is-Contr : (h : A → A) → isContr (fib (λ g → g ∘ f) h)
    fib-of-post-∘-is-Contr = ishae-to-isContrMap (λ g → g ∘ f) (qinv-to-ishae (pre-∘-by-qinv-is-qinv A f q))


-- Definition 4.2.10 (Coherence data)

lcoh : {A : 𝓤 ̇} {B : 𝓥 ̇} (f : A → B) → ret f → 𝓤 ⊔ 𝓥 ̇ 
lcoh {𝓤} {𝓥} {A} {B} f (g , η) = Σ ε ꞉ (f ∘ g ∼ id) , ((y : B) → ap g (ε y) ≡ η (g y))

rcoh : {A : 𝓤 ̇} {B : 𝓥 ̇} (f : A → B) → sec f → 𝓤 ⊔ 𝓥 ̇ 
rcoh {𝓤} {𝓥} {A} {B} f (g , ε) = Σ η ꞉ (g ∘ f ∼ id) , ((x : A) → ap f (η x) ≡ ε (f x))


-- Lemma 4.2.11 (Characterization of coherence data in terms of fibers).

module coh-≃-fib {A : 𝓤 ̇} {B : 𝓥 ̇} (f : A → B) where

  fib-to-rcoh : (σ : sec f) → ((x : A) → pr₁ σ (f x) , pr₂ σ (f x) ≡ x , refl (f x)) →  rcoh f σ
  fib-to-rcoh (g , ε) h = (λ x → pr₁ (k x)) , (λ x → ru _ ∙ pr₂ (k x))
    where
    k : (x : A) → Σ p ꞉ g (f x) ≡ x , (ap f p ∙ refl (f x) ≡ ε (f x))
    k = λ x → pr₁ (path-space-fib _ _) (h x)
    
  module _ ⦃ fe : FunExt ⦄ where  

    lcoh-≃-fib : (ρ : ret f) → lcoh f ρ ≃ ((y : B) → f (pr₁ ρ y) , pr₂ ρ (pr₁ ρ y) ≡ y , refl (pr₁ ρ y))
    lcoh-≃-fib (g , η) = ≃-sym (Π-preserves-family-≃ by-path-space-fib ● split , dep-Σ-UMP _ _ _)
      where  
      by-path-space-fib : (y : B) → (f (g y) , η (g y) ≡ y , refl (g y)) ≃ (Σ γ ꞉ (f (g y) ≡ y) , (ap g (γ) ≡ η (g y))) 
      by-path-space-fib y = path-space-fib (f (g y) , η (g y)) (y , refl (g y)) ● Σ-preserves-family-≃ (λ γ → pre-∙-≃ _ (ru (ap g γ))) 

    rcoh-≃-fib : (σ : sec f) → rcoh f σ ≃ ((x : A) → pr₁ σ (f x) , pr₂ σ (f x) ≡ x , refl (f x))
    rcoh-≃-fib (g , ε) = ≃-sym (Π-preserves-family-≃ by-path-space-fib ● split , dep-Σ-UMP _ _ _)
      where  
      by-path-space-fib : (x : A) → (g (f x) , ε (f x) ≡ x , refl (f x)) ≃ (Σ γ ꞉ (g (f x) ≡ x) , (ap f (γ) ≡ ε (f x))) 
      by-path-space-fib x = path-space-fib (g (f x) , ε (f x)) (x , refl (f x)) ● Σ-preserves-family-≃ (λ γ → (ru (ap f γ) ∙_) , (qinv-to-isequiv (qinv-pre-∙ _ _))) 

open coh-≃-fib public 


module _ ⦃ fe : FunExt ⦄ where

  -- Lemma 4.2.12 (Right coherence-data of haes is contractible)

  rcoh-of-hae-is-Contr : {A : 𝓤 ̇} {B : 𝓥 ̇} (f : A → B) → ishae f → (σ : sec f) → isContr (rcoh f σ)
  rcoh-of-hae-is-Contr f h (g , ε) = retract-of-Contr-is-Contr (≃-to-◁ (≃-sym (rcoh-≃-fib f (g , ε)))) (Π-preserves-Contr _ λ x → pr₁ Prop-iff-Contr-≡ (isContr-to-isProp (ishae-to-isContrMap f h (f x))) _ _)


  -- Theorem 4.2.13 (ishae is a proposition).

  ishae-is-Prop : {A : 𝓤 ̇} {B : 𝓥 ̇} (f : A → B) → isProp (ishae f)
  ishae-is-Prop {𝓤} {𝓥} {A} {B} f = suffices λ h → retract-of-Contr-is-Contr (≃-to-◁ equivalence) (Σ-preserves-Contr (sec-of-qinv-is-Contr f (ishae-to-qinv h)) (rcoh-of-hae-is-Contr f h))
    where
    suffices : (ishae f → isContr (ishae f)) → isProp (ishae f)
    suffices = inv (isProp-≃-inhabited-to-isContr (ishae f))
    equivalence : Σ (λ (u : sec f) → rcoh f u) ≃ ishae f
    equivalence =
      Σ (λ (u : sec f) → rcoh f u)
        ≃⟨ ≃-sym (Σ-assoc _ _ (λ (u : sec f) → rcoh f u)) ⟩
      (Σ λ (g : B → A) → Σ λ (ε : f ∘ g ∼ id) → rcoh f (g , ε))
        ≃⟨ Σ-preserves-family-≃ (λ g → Σ-swap _ _ _) ⟩
      ishae f ■

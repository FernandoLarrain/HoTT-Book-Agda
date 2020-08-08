{-# OPTIONS --without-K --exact-split --safe #-}

open import Ch1.Type-theory
open import Ch2.Homotopy-type-theory
open import Ch3.Sets-and-logic
open import Ch4.2-Half-adjoint-equivalences
open import Ch4.3-Bi-invertible-maps
open import Ch4.4-Contractible-fibers
open import Ch4.5-On-the-definition-of-equivalences
open import Ch4.6-Surjections-and-embeddings

module Ch4.7-Closure-properties-of-equivalences where


-- Theorem 7.4.1 (2-out-of-3 property).

module 2-out-of-3 {A : 𝓤 ̇} {B : 𝓥 ̇} {C : 𝓦 ̇} (f : A → B) (g : B → C) where

  -∘ : (isequiv f → isequiv g → isequiv (g ∘ f))
  -∘ ief ieg = pr₂ (f , ief ● g , ieg)
 
  -∘-is-Prop :  ⦃ fe : FunExt ⦄ → isProp (isequiv f → isequiv g → isequiv (g ∘ f))
  -∘-is-Prop = →-preserves-Props _ _ (→-preserves-Props _ _ (ishae-is-Prop _))

  first : (isequiv g → isequiv (g ∘ f) → isequiv f)
  first ieg ie∘ = qinv-to-isequiv ((isequiv₁ ie∘ ∘ g) , (
    (λ b →
      f (isequiv₁ ie∘ (g b))
        ≡⟨ isequiv₂ ieg _ ⁻¹ ⟩
      isequiv₁ ieg ( g (f (isequiv₁ ie∘ (g b))))
        ≡⟨ ap (isequiv₁ ieg) (isequiv₃ ie∘ _)  ⟩
      isequiv₁ ieg (g b)
        ≡⟨ isequiv₂ ieg b ⟩
      b ∎ 
      ) ,
    isequiv₂ ie∘ 
    ))
  
  first-is-Prop : ⦃ fe : FunExt ⦄ → isProp (isequiv g → isequiv (g ∘ f) → isequiv f)
  first-is-Prop = →-preserves-Props _ _ (→-preserves-Props _ _ (ishae-is-Prop _))
  
  second : (isequiv f → isequiv (g ∘ f) → isequiv g)
  second ief ie∘ = qinv-to-isequiv ((f ∘ isequiv₁ ie∘) , (
    (isequiv₃ ie∘) ,
    (λ b →
      f (isequiv₁ ie∘ (g b))
        ≡⟨ ap (f ∘ isequiv₁ ie∘ ∘ g) (isequiv₃ ief b ⁻¹) ⟩
      f (isequiv₁ ie∘ (g (f (isequiv₁ ief b))))
        ≡⟨ ap f (isequiv₂ ie∘ _) ⟩
      f (isequiv₁ ief b)
        ≡⟨ isequiv₃ ief b ⟩
      b ∎)
    ))

  second-is-Prop : ⦃ fe : FunExt ⦄ → isProp (isequiv f → isequiv (g ∘ f) → isequiv g)
  second-is-Prop = →-preserves-Props _ _ (→-preserves-Props _ _ (ishae-is-Prop _))


-- Definition 4.7.2 (Retract of function).

_is-retract-of_ : {A : 𝓤 ̇} {B : 𝓥 ̇} {X : 𝓦 ̇} {Y : 𝓣 ̇} (g : A → B) (f : X → Y) → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ⊔ 𝓣 ̇ 
_is-retract-of_ {A = A} {B} {X} {Y} g f =
  Σ ρ ꞉ A ◁ X ,
  Σ ρ' ꞉ B ◁ Y ,
  Σ hsec ꞉ f ∘ section ρ ∼ section ρ' ∘ g ,
  Σ hret ꞉ g ∘ retraction ρ ∼ retraction ρ' ∘ f ,
  ((a : A) → ap g (retraction-eqn ρ a) ∙ retraction-eqn ρ' (g a) ⁻¹ ≡ hret (section ρ a) ∙ ap (retraction ρ') (hsec a))

codom-retraction : {A : 𝓤 ̇} {B : 𝓥 ̇} {X : 𝓦 ̇} {Y : 𝓣 ̇} (g : A → B) (f : X → Y) → g is-retract-of f → Y → B
codom-retraction g f (ρ , ρ' , etc) = retraction ρ'

codom-section : {A : 𝓤 ̇} {B : 𝓥 ̇} {X : 𝓦 ̇} {Y : 𝓣 ̇} (g : A → B) (f : X → Y) → g is-retract-of f → B → Y
codom-section g f (ρ , ρ' , etc) = section ρ'

dom-retraction : {A : 𝓤 ̇} {B : 𝓥 ̇} {X : 𝓦 ̇} {Y : 𝓣 ̇} (g : A → B) (f : X → Y) → g is-retract-of f → X → A
dom-retraction g f (ρ , etc) = retraction ρ

dom-section : {A : 𝓤 ̇} {B : 𝓥 ̇} {X : 𝓦 ̇} {Y : 𝓣 ̇} (g : A → B) (f : X → Y) → g is-retract-of f → A → X
dom-section g f (ρ , etc) = section ρ


-- Lemma 4.7.3 (Retractions of maps induce retractions of fibers).

retraction-of-maps-to-fiberwise-retraction : ⦃ fe : FunExt ⦄ {A : 𝓤 ̇} {B : 𝓥 ̇} {X : 𝓦 ̇} {Y : 𝓣 ̇} (g : A → B) (f : X → Y) → (ρ : g is-retract-of f) → (b : B) → fib g b ◁ fib f (codom-section _ _ ρ b)
retraction-of-maps-to-fiberwise-retraction {𝓤} {𝓥} {𝓦} {𝓣} {A} {B} {X} {Y} g f ((r , s , R) , (r' , s' , R') , L , K , H) b = (ψ b) , ((ϕ b) , (retraction-equation b))

  where 

  ϕ : (b : B) → fib g b → fib f (s' b) 
  ϕ b (a , p) = (s a) , (L a ∙ ap s' p)
  
  ψ : (b : B) → fib f (s' b) → fib g b
  ψ b (x , q) = (r x) , (K x ∙ ap r' q ∙ R' b)
  
  equivalence : ((b : B) → ψ b ∘ ϕ b ∼ id) ≃ ((a : A) → ψ (g a) (ϕ (g a) (a , refl (g a))) ≡ (a , refl (g a)))
  equivalence = Π-preserves-family-≃ (λ b → GCCAdj A (λ a → g a ≡ b) _) ● (Π-swap B A _ ● Π-preserves-family-≃ (λ a → ≃-sym (GCCAdj B (λ b → g a ≡ b) _) ● Π-over-Contr-base-is-fib _ _ (free-right-endpt-is-Contr _ (g a))))
  
  transport-lemma : (a a' : A) (p : a ≡ a') (b : B) (q : g a ≡ b) → transport (λ - → g - ≡ b) p q ≡ ap g (p ⁻¹) ∙ q  
  transport-lemma a a (refl a) b q = lu _
  
  retraction-equation : (b : B) → ψ b ∘ ϕ b ∼ id
  retraction-equation = isequiv₁ (pr₂ equivalence) (λ a → dpair-≡ ((R a) , (
    transport-lemma _ _ (R a) (g a) _ ∙
    ap (λ - → ap g (R a ⁻¹) ∙ (K (s a) ∙ ap r' - ∙ R' (g a))) (ru _ ⁻¹) ∙
    ap (λ - → ap g (R a ⁻¹) ∙ (- ∙ R' (g a))) (H a ⁻¹) ∙
    ap (λ - → ap g (R a ⁻¹) ∙ -) (∙-assoc _ _ _ ⁻¹ ∙ (ap g (R a) ∙ₗ linv _) ∙ ru _ ⁻¹) ∙
    ap-∙ _ _ _ ⁻¹ ∙ ap (ap g) (linv _))))


-- Theorem 4.7.4 (A retract of an equivalence is an equivalence).

retract-of-ContrMap-is-ContrMap : ⦃ fe : FunExt ⦄ {A : 𝓤 ̇} {B : 𝓥 ̇} {X : 𝓦 ̇} {Y : 𝓣 ̇} (g : A → B) (f : X → Y) → isContrMap f → g is-retract-of f → isContrMap g
retract-of-ContrMap-is-ContrMap g f c ρ y = retract-of-Contr-is-Contr (retraction-of-maps-to-fiberwise-retraction g f ρ y) (c _)


-- Definition 4.7.5 (Map of total spaces induced by fiberwise map / transformation).

total : {A : 𝓤 ̇} {P : A → 𝓥 ̇} {Q : A → 𝓦 ̇} (f : Π (λ x → P x → Q x)) → Σ P → Σ Q
total f (x , u) = x , (f x u)


-- Theorem 4.7.6 (Equivalence of fibers)

total-fib-≃ : {A : 𝓤 ̇} {P : A → 𝓥 ̇} {Q : A → 𝓦 ̇} (f : Π (λ x → P x → Q x)) (x : A) (v : Q x) → fib (total f) (x , v) ≃ fib (f x) v
total-fib-≃ {𝓤} {𝓥} {𝓦} {A} {P} {Q} f x v =
  fib (total f) (x , v)
    ≃⟨ ≃-sym (Σ-assoc A P _) ⟩
  (Σ a ꞉ A , Σ u ꞉ P a , (a , f a u) ≡ (x , v))
    ≃⟨ Σ-preserves-family-≃ (λ a → Σ-preserves-family-≃ λ u → Σ-≡-equiv) ⟩
  (Σ a ꞉ A , Σ u ꞉ P a , Σ p ꞉ a ≡ x , transport Q p (f a u) ≡ v)
    ≃⟨ Σ-preserves-family-≃ (λ a → Σ-swap _ _ _) ⟩
  (Σ a ꞉ A , Σ p ꞉ a ≡ x , Σ u ꞉ P a , transport Q p (f a u) ≡ v)
    ≃⟨ Σ-assoc _ _ _ ⟩
  (Σ w ꞉ (Σ a ꞉ A , a ≡ x) , Σ u ꞉ P (pr₁ w) , transport Q (pr₂ w) (f (pr₁ w) u) ≡ v)
    ≃⟨ Σ-over-Contr-base-is-fib _ _ (free-left-endpt-is-Contr _ _) ⟩
  (Σ u ꞉ P x , f x u ≡ v)
    ≃⟨ ≃-refl _ ⟩
  fib (f x) v ■


-- Theorem 4.7.7 (Fiberwise equivalence iff total equivalence).

{- Note : one direction is just that Σ preserves fiberwise equivalences, i.e. Σ-preserves-family-≃. -}

module fiberwise-≃-iff-total-≃ {A : 𝓤 ̇} {P : A → 𝓥 ̇} {Q : A → 𝓦 ̇} (f : Π (λ x → P x → Q x)) where

  Contr : ((x : A) → isContrMap (f x)) ⇔ isContrMap (total f)
  Contr = sufficiency , necessity where
    sufficiency : ((x : A) → isContrMap (f x)) → isContrMap (total f)
    sufficiency f-is-Contr (x , v) = retract-of-Contr-is-Contr (≃-to-◁ (≃-sym (total-fib-≃ f x v))) (f-is-Contr x v)
    necessity : isContrMap (total f) → ((x : A) → isContrMap (f x))
    necessity t-is-Contr x v = retract-of-Contr-is-Contr (≃-to-◁ (total-fib-≃ f x v)) (t-is-Contr (x , v))

  Hae : ((x : A) → ishae (f x)) ⇔ ishae (total f)
  Hae = sufficiency , necessity where
    sufficiency : ((x : A) → ishae (f x)) → ishae (total f)
    sufficiency f-is-hae = isContrMap-to-ishae (total f) (pr₁ Contr (λ x → ishae-to-isContrMap (f x) (f-is-hae x)))
    necessity : ishae (total f) → ((x : A) → ishae (f x))
    necessity t-is-hae x = isContrMap-to-ishae (f x) (pr₂ Contr (ishae-to-isContrMap (total f) t-is-hae) x)

  Biinv : ⦃ fe : FunExt ⦄ → (((x : A) → biinv (f x)) ⇔ biinv (total f))
  Biinv = sufficiency , necessity where
    sufficiency : ((x : A) → biinv (f x)) → biinv (total f)
    sufficiency f-is-hae = isContrMap-to-biinv (total f) (pr₁ Contr (λ x → biinv-to-isContrMap (f x) (f-is-hae x)))
    necessity : biinv (total f) → ((x : A) → biinv (f x))
    necessity t-is-hae x = isContrMap-to-biinv (f x) (pr₂ Contr (biinv-to-isContrMap (total f) t-is-hae) x)


-- Sufficient condition for embedding.

embedding-criterion : {A : 𝓤 ̇} {B : 𝓥 ̇} (f : A → B) → ((x x' : A) → (f x ≡ f x') ≃ (x ≡ x')) → is-embedding f
embedding-criterion {𝓤} {𝓥} {A} {B} f e x = pr₂ (fiberwise-≃-iff-total-≃.Hae (λ x' → ap f {x} {x'})) (map-between-Contrs-is-equiv (total (λ x' → ap f)) (free-right-endpt-is-Contr _ x) (≃-preserves-Contr (≃-sym aux-equiv) (free-right-endpt-is-Contr _ x)))
  where
  e₁ : (x' : A) → f x ≡ f x' → x ≡ x'
  e₁ x' = pr₁ (e x x')
  e₁-is-fiberwise-equiv : (x' : A) → isequiv (e₁ x')
  e₁-is-fiberwise-equiv x' = pr₂ (e x x')
  aux-equiv : (Σ x' ꞉ A , f x ≡ f x') ≃ (Σ x' ꞉ A , x ≡ x')
  aux-equiv = (total e₁) , (pr₁ (fiberwise-≃-iff-total-≃.Hae e₁) e₁-is-fiberwise-equiv)


-- Example: Lift is an embedding of one universe into another.

Lift-is-embedding : ⦃ fe : FunExt ⦄ ⦃ univ : Univalence ⦄ → is-embedding (Lift {𝓤} 𝓥)
Lift-is-embedding {𝓤} {𝓥} = embedding-criterion (Lift 𝓥) (λ A B → (idtoeqv , idtoeqv-is-equiv) ● (≃-preserves-left-≃ (Lift 𝓥 B) Lift-≃ ● ≃-preserves-right-≃ A Lift-≃) ●  ≃-sym (idtoeqv , idtoeqv-is-equiv))

{-# OPTIONS --without-K --exact-split --safe #-}

open import Ch1.Type-theory
open import Ch2.Homotopy-type-theory
open import Ch3.Sets-and-logic
open import Ch4.Equivalences
--open import Ch5.4-Inductive-types-are-initial-algebras
open import Ch5.8-Id-types-and-id-systems
--open import Ch6.4-Circles-and-spheres-safe
--open import Ch6.5-Suspensions-safe

module int-as-HIT.Z-algebras where


-- General definitions / results.

PathOver² : {A : 𝓤 ̇} (P : A → 𝓥 ̇) {x y : A} {p q : x ≡ y} (r : p ≡ q) {u : P x} {v : P y} (h : u ≡ v [ P ↓ p ]) (k : u ≡ v [ P ↓ q ]) → 𝓥 ̇
PathOver² P {x} {y} r {u} {v} h k = h ≡ k [ (λ (- : x ≡ y) → u ≡ v [ P ↓ - ]) ↓ r ]

infix 0 PathOver²

syntax PathOver² P r h k = h ≡ k [ P ⇊ r ]


ap-over : {X : 𝓤 ̇} {Y : 𝓥 ̇} (P : X → 𝓦 ̇) (Q : Y → 𝓣 ̇) (f : X → Y) (g : (x : X) → P x → Q (f x)) {x₁ x₂ : X} (p : x₁ ≡ x₂) {u₁ : P x₁} {u₂ : P x₂} → u₁ ≡ u₂ [ P ↓ p ] → g x₁ u₁ ≡ g x₂ u₂ [ Q ↓ ap f p ]
ap-over P Q f g (refl _) q = ap (g _) q


ap-dpair : {X : 𝓤 ̇} {Y : X → 𝓥 ̇} (f : X → X) (g : (x : X) → Y x → Y (f x)) {x x' : X} {y : Y x} {y' : Y x'} (p : x ≡ x') (q : y ≡ y' [ Y ↓ p ]) → ap {_} {_} {Σ Y} {Σ Y} (Σ-induction (λ x y → f x , g x y)) (dpair-≡ (p , q)) ≡ dpair-≡ ((ap f p) , ap-over Y Y f g p q)
ap-dpair f g (refl _) (refl _) = refl _


-- ℤ-algebras and their homomorphisms

Eqv : (𝓤 : Universe) → 𝓤 ⁺ ̇
Eqv 𝓤 = Σ A₁ ꞉ (𝓤 ̇) , Σ A₂ ꞉ (𝓤 ̇) , A₁ ≃ A₂ -- It suffices to consider types in a single universe.


module EqvPreservation {A₁ A₂ : 𝓤 ̇} {B₁ B₂ : 𝓥 ̇} (f₁ : A₁ → B₁) (f₂ : A₂ → B₂) where

  module maps where

  s-pres : (A₁ → A₂) → (B₁ → B₂) → 𝓤 ⊔ 𝓥 ̇
  s-pres s s' = f₂ ∘ s ∼ s' ∘ f₁

  p-pres : (A₂ → A₁) → (B₂ → B₁) → 𝓤 ⊔ 𝓥 ̇
  p-pres p p' = f₁ ∘ p ∼ p' ∘ f₂


  module htpies (s : A₁ → A₂) (p : A₂ → A₁) (s' : B₁ → B₂) (p' : B₂ → B₁) (α : s-pres s s') (β : p-pres p p') where

    aux-γ : f₁ ∘ p ∘ s ∼ p' ∘ s' ∘ f₁
    aux-γ a₁ = β (s a₁) ∙ ap p' (α a₁)

    σ-pres : (p ∘ s ∼ id) → (p' ∘ s' ∼ id) → 𝓤 ⊔ 𝓥 ̇
    σ-pres σ σ' = (a₁ : A₁) → ap f₁ (σ a₁) ≡ aux-γ a₁ ∙ σ' (f₁ a₁)

    aux-δ : f₂ ∘ s ∘ p ∼ s' ∘ p' ∘ f₂
    aux-δ a₂ = α (p a₂) ∙ ap s' (β a₂)

    ρ-pres : (s ∘ p ∼ id) → (s' ∘ p' ∼ id) → 𝓤 ⊔ 𝓥 ̇
    ρ-pres ρ ρ' = (a₂ : A₂) → ap f₂ (ρ a₂) ≡ aux-δ a₂ ∙ ρ' (f₂ a₂)

    -- Preservation of coherence condition

    aux-ε-γ₁ : f₂ ∘ s ∘ p ∘ s ∼ s' ∘ p' ∘ s' ∘ f₁
    aux-ε-γ₁ a₁ = α (p (s a₁)) ∙ ap s' (aux-γ a₁)

    aux-ε-δ₁ : f₂ ∘ s ∘ p ∘ s ∼ s' ∘ p' ∘ s' ∘ f₁
    aux-ε-δ₁ a₁ = aux-δ (s a₁) ∙ ap s' (ap p' (α a₁))

    aux-ε-γ₁-is-aux-ε-δ₁ : aux-ε-γ₁ ∼ aux-ε-δ₁
    aux-ε-γ₁-is-aux-ε-δ₁ a₁ = (refl (α (p (s a₁))) ✦ ap-∙ s' _ _) ∙ ∙-assoc _ _ _

    aux-ε-γ₂ : (σ : p ∘ s ∼ id) (σ' : p' ∘ s' ∼ id) → ((a₁ : A₁) → ap f₁ (σ a₁) ≡ aux-γ a₁ ∙ σ' (f₁ a₁)) → (a₁ : A₁) → ap f₂ (ap s (σ a₁)) ∙ α a₁ ≡ aux-ε-γ₁ a₁ ∙ ap s' (σ' (f₁ a₁))
    aux-ε-γ₂ σ σ' γ a₁ = (ap-∘ s f₂ (σ a₁) ✦ refl (α a₁)) ∙ hnat α (σ a₁) ⁻¹ ∙ (refl (α (p (s a₁))) ✦ (ap-∘ f₁ s' (σ a₁) ⁻¹ ∙ ap (ap s') (γ a₁) ∙ ap-∙ s' _ _)) ∙ ∙-assoc _ _ _

    aux-ε-δ₂ : (ρ : s ∘ p ∼ id) (ρ' : s' ∘ p' ∼ id) → ((a₂ : A₂) → ap f₂ (ρ a₂) ≡ aux-δ a₂ ∙ ρ' (f₂ a₂)) → (a₁ : A₁) → ap f₂ (ρ (s a₁)) ∙ α a₁ ≡ aux-ε-δ₁ a₁ ∙ ρ' (s' (f₁ a₁))
    aux-ε-δ₂ ρ ρ' δ a₁ = (δ (s a₁) ✦ ap-id (α a₁) ⁻¹) ∙ ∙-assoc _ _ _ ⁻¹ ∙ (refl (aux-δ (s a₁)) ✦ (hnat ρ' (α a₁) ∙ (ap-∘ p' s' (α a₁) ⁻¹ ✦ refl (ρ' (s' (f₁ a₁)))))) ∙ ∙-assoc _ _ _  

    module coh (σ : p ∘ s ∼ id) (ρ : s ∘ p ∼ id) (τ : (a₁ : A₁) → ap s (σ a₁) ≡ ρ (s a₁)) (σ' : p' ∘ s' ∼ id) (ρ' : s' ∘ p' ∼ id) (τ' : (b₁ : B₁) → ap s' (σ' b₁) ≡ ρ' (s' b₁)) (γ : σ-pres σ σ') (δ : ρ-pres ρ ρ') where

      τ-pres : 𝓤 ⊔ 𝓥 ̇
      τ-pres = (a₁ : A₁) → (ap (ap f₂) (τ a₁) ✦ refl (α a₁)) ∙ aux-ε-δ₂ ρ ρ' δ a₁ ≡ aux-ε-γ₂ σ σ' γ a₁ ∙ (aux-ε-γ₁-is-aux-ε-δ₁ a₁ ✦ τ' (f₁ a₁))


hae-pres : (A : Eqv 𝓤) (B : Eqv 𝓥) → (pr₁ A → pr₁ B) → (pr₁ (pr₂ A) → pr₁ (pr₂ B)) → 𝓤 ⊔ 𝓥 ̇
hae-pres (A₁ , A₂ , s , p , σ , ρ , τ) (B₁ , B₂ , s' , p' , σ' , ρ' , τ') f₁ f₂ =
  Σ α ꞉ s-pres s s' ,
  Σ β ꞉ p-pres p p' ,
  Σ γ ꞉ σ-pres α β σ σ' ,
  Σ δ ꞉ ρ-pres α β ρ ρ' ,
  τ-pres α β σ ρ τ σ' ρ' τ' γ δ
  where open EqvPreservation f₁ f₂
        open maps
        open htpies s p s' p'
        open coh


EqvHom : Eqv 𝓤 → Eqv 𝓥 → 𝓤 ⊔ 𝓥 ̇
EqvHom A B = Σ f₁ ꞉ (pr₁ A → pr₁ B) , Σ f₂ ꞉ (pr₁ (pr₂ A) → pr₁ (pr₂ B)) , hae-pres A B f₁ f₂ 


ℤAlg : (𝓤 : Universe) → 𝓤 ⁺ ̇
ℤAlg 𝓤 = Σ A ꞉ (𝓤 ̇) ,
         Σ a₀ ꞉ A ,
         Σ s ꞉ (A → A) ,
         Σ p ꞉ (A → A) ,
         Σ σ ꞉ (p ∘ s ∼ id) ,
         Σ ρ ꞉ (s ∘ p ∼ id) ,
         ((a : A) → ap s (σ a) ≡ ρ (s a))

_ : (𝓤 : Universe) → ℤAlg 𝓤 ≡ (Σ A ꞉ (𝓤 ̇) , Σ a₀ ꞉ A , A ≃ A)
_ = λ 𝓤 → refl _


ℤHom : ℤAlg 𝓤 → ℤAlg 𝓥 → 𝓤 ⊔ 𝓥 ̇
ℤHom (A , a₀ , s) (B , b₀ , s') = Σ f ꞉ (A → B) , Σ p₀ ꞉ (f a₀ ≡ b₀) , hae-pres (A , A , s) (B , B , s') f f


-- Can we work with simpler homomorphisms?

module _ (A : 𝓤 ̇) (B : 𝓥 ̇) (f : A → B) where

  open EqvPreservation f f
  open maps

  module _ (β : p-pres id id) where

    open htpies id id id id (hrefl f) (hrefl f)

    module _ (γ : σ-pres (hrefl _) (hrefl _)) (δ : ρ-pres (hrefl _) (hrefl _)) where

      open coh (hrefl _) (hrefl _) (hrefl _) (hrefl _) (hrefl _) (hrefl _) γ δ

      module _ (ε : τ-pres) (a : A) where

        _ : {!!} -- if α is refl (𝕁-∼), then β is, and then γ ≡ δ. But there's no way to show that γ, δ and ε are trivial.
        _ = {!!}

-- simple-homs : ⦃ fe : FunExt ⦄ ⦃ univ : Univalence ⦄ (A₁ A₂ : 𝓤 ̇) (e : A₁ ≃ A₂) (B₁ B₂ : 𝓥 ̇) (e' : B₁ ≃ B₂) (f₁ : A₁ → B₁) (f₂ : A₂ → B₂) → hae-pres (A₁ , A₂ , e) (B₁ , B₂ , e') f₁ f₂ ≃ (f₂ ∘ pr₁ e ≡ pr₁ e' ∘ f₁)
-- simple-homs {𝓤} {𝓥} = 𝕁-≃ (λ A₁ A₂ e → (B₁ B₂ : 𝓥 ̇) (e' : B₁ ≃ B₂) (f₁ : A₁ → B₁) (f₂ : A₂ → B₂) → hae-pres (A₁ , A₂ , e) (B₁ , B₂ , e') f₁ f₂ ≃ (f₂ ∘ pr₁ e ≡ pr₁ e' ∘ f₁)) λ A →
--   𝕁-≃ (λ B₁ B₂ e' → (f₁ : A → B₁) (f₂ : A → B₂) → hae-pres (A , A , ≃-refl A) (B₁ , B₂ , e') f₁ f₂ ≃ (f₂ ∘ id ≡ pr₁ e' ∘ f₁))
--   λ B f₁ f₂ →
--     {!!}


-- -- Fibered ℤ-algebras and their sections


-- module _ (A : 𝓤 ̇) (a₀ : A) (s : A → A) (p : A → A) (σ : p ∘ s ∼ id) (ρ : s ∘ p ∼ id) (τ : (a : A) → ap s (σ a) ≡ ρ (s a)) (P : A → 𝓥 ̇) (u₀ : P a₀) (sₚ : (a : A) (u : P a) → P (s a)) (pₚ : (a : A) (u : P a) → P (p a)) (σₚ : (a : A) (u : P a) → pₚ (s a) (sₚ a u) ≡ u [ P ↓ σ a ]) (ρₚ : (a : A) (u : P a) → sₚ (p a) (pₚ a u) ≡ u [ P ↓ ρ a ]) (τₚ : (a : A) (u : P a) → ap-over P P s sₚ (σ a) (σₚ a u) ≡ ρₚ (s a) (sₚ a u) [ P ⇊ τ a ]) where

--   -- The data allow us to define a ℤ-algebra structure on Σ P

--   sₜ : Σ P → Σ P
--   sₜ (a , u) = (s a) , sₚ a u
  
--   pₜ : Σ P → Σ P
--   pₜ (a , u) = (p a) , pₚ a u
  
--   σₜ : pₜ ∘ sₜ ∼ id
--   σₜ (a , u) = dpair-≡ ((σ a) , (σₚ a u))
  
--   ρₜ : sₜ ∘ pₜ ∼ id
--   ρₜ (a , u) = dpair-≡ ((ρ a) , (ρₚ a u))
  
--   τₜ : (t : Σ P) → ap sₜ (σₜ t) ≡ ρₜ (sₜ t)
--   τₜ (a , u) = ap-dpair s sₚ (σ a) (σₚ a u) ∙ ap dpair-≡ (dpair-≡ (τ a , τₚ a u))

--   T : ℤAlg (𝓤 ⊔ 𝓥)
--   T = (Σ P) , (a₀ , u₀) , sₜ , pₜ , σₜ , ρₜ , τₜ

--   -- Is pr₁ a homomorphism?

--   open EqvPreservation {_} {_} {Σ P} {Σ P} {A} {A} pr₁ pr₁
--   open maps
--   open htpies sₜ pₜ s p (hrefl _) (hrefl _)

--   _ : aux-γ ∼ hrefl _
--   _ = hrefl _

--   _ : aux-δ ∼ hrefl _
--   _ = hrefl _

--   _ : aux-ε-γ₁ ∼ hrefl _
--   _ = hrefl _

--   _ : aux-ε-δ₁ ∼ hrefl _
--   _ = hrefl _

--   _ : aux-ε-γ₁-is-aux-ε-δ₁ ∼ hrefl _
--   _ = hrefl _

--   γ : (w : Σ P) → ap pr₁ (σₜ w) ≡ aux-γ w ∙ σ (pr₁ w)
--   γ (a , u) = dpr₁-≡-β (σ a) (σₚ a u) ∙ lu _

--   δ : (w : Σ P) → ap pr₁ (ρₜ w) ≡ aux-δ w ∙ ρ (pr₁ w)
--   δ (a , u) = dpr₁-≡-β (ρ a) (ρₚ a u) ∙ lu _

--   open coh σₜ ρₜ τₜ σ ρ τ γ δ

--   _ : aux-ε-γ₂ σₜ σ γ ∼ λ w → {!!} -- hnat?
--   _ = {!!}

--   _ : aux-ε-δ₂ ρₜ ρ δ ∼ λ w → ru _ ⁻¹ ∙ δ (sₜ w)
--   _ = Σ-induction λ a u → {!!}

--   ε : τ-pres -- τ-pres
--   ε (a , u) =
--     (ap (ap pr₁) (τₜ (a , u)) ✦ refl (refl _)) ∙ ((δ (sₜ (a , u)) ✦ refl (refl _)) ∙ ∙-assoc _ _ _ ⁻¹ ∙ (refl (refl _) ✦ (ru _ ⁻¹ ∙ lu _ ∙ (refl _ ✦ refl _))) ∙ ∙-assoc _ _ _  )
--       ≡⟨ {!!} ⟩
--     {!!}
--       ≡⟨ {!!} ⟩
--     {!!}
--       ≡⟨ {!!} ⟩
--     {!!}

--   π₁ : ℤHom (Σ P , (a₀ , u₀) , sₜ , pₜ , σₜ , ρₜ , τₜ) (A , a₀ , s , p , σ , ρ , τ)
--   π₁ = pr₁ , refl _ , (hrefl _) , (hrefl _) , γ , δ , ε

{-# OPTIONS --without-K --exact-split #-}

open import Ch1.Type-theory
open import Ch2.Homotopy-type-theory
open import Ch3.Sets-and-logic
open import Ch4.Equivalences

module Ch5.Exercises where


-- Exercise: characterization of Π-types (a dependent function is a section of the projection of total space).

module _ {A : 𝓤 ̇} {B : 𝓥 ̇} (f : A → B) {g h : sec f} where

  sec-≡ : (g ≡ h) ≃ (Σ α ꞉ pr₁ g ∼ pr₁ h , ((y : B) → ap f (α y) ⁻¹ ∙ pr₂ g y ≡ pr₂ h y)) 
  sec-≡ = Σ-≡-≃ ● Σ-preserves-≃ _ _ (happly , happly-is-equiv) λ p → (happly , happly-is-equiv) ● Π-preserves-family-≃ (λ y → (transport-lemma ⁻¹ ∙_) , (qinv-to-isequiv (qinv-pre-∙ _ _))) where
    transport-lemma : {p : pr₁ g ≡ pr₁ h} {y : B} →  transport (λ s → f ∘ s ∼ id) p (pr₂ g) y ≡ ap f (happly p y) ⁻¹ ∙ pr₂ g y
    transport-lemma {refl .(fst g)} = lu _

module dfuns-are-sections {A : 𝓤 ̇} (B : A → 𝓥 ̇) where

  ϕ : Π B → sec {_} {_} {Σ B} pr₁
  ϕ f = (λ a → a , (f a)) , (hrefl _)

  ψ : sec {_} {_} {Σ B} pr₁ → Π B
  ψ (g , s) = λ a → transport B (s a) (pr₂ (g a))

  α : ϕ ∘ ψ ∼ id
  α (g , s) = inv (sec-≡ pr₁) ((λ a → dpair-≡ ((s a ⁻¹) , (transport-∙ B (s a) (s a ⁻¹) (pr₂ (g a)) ∙ ap (λ - → transport B - (pr₂ (g a))) (rinv (s a))))) , λ a → ru _ ⁻¹ ∙ (ap _⁻¹ (dpr₁-≡-β _ _) ∙ ⁻¹-invol _))

  β : ψ ∘ ϕ ∼ id
  β f = refl _

  equiv : Π B ≃ sec {_} {_} {Σ B} pr₁ 
  equiv = ϕ , (qinv-to-isequiv (ψ , (α , β)))

-- Exercise: characterization of families of functions over a function.

module families-of-funs↓ {A : 𝓤 ̇} {B : 𝓥 ̇} (f : A → B) (P : A → 𝓦 ̇) (Q : B → 𝓣 ̇) where

  tot-≡ : (F G : (Σ t ꞉ (Σ P → Σ Q) , pr₁ ∘ t ∼ f ∘ pr₁)) (H : pr₁ F ∼ pr₁ G) → pr₂ F ∼ (λ w → ap pr₁ (H w) ∙ pr₂ G w) → F ≡ G
  tot-≡ (t₁ , α) (t₂ , β) H 𝓗 = dpair-≡ (funext H , transport-lemma (funext H) (transport (λ - → α ∼ (λ w → ap pr₁ (- w) ∙ β w)) (funext (happly-β H) ⁻¹) 𝓗))
    where
    transport-lemma : (p : t₁ ≡ t₂) → α ∼ (λ w → ap pr₁ (happly p w) ∙ β w) → transport (λ t → pr₁ ∘ t ∼ f ∘ pr₁) p α ≡ β
    transport-lemma (refl t) 𝓗 = funext (λ w → 𝓗 w ∙ lu _ ⁻¹)

  ϕ :  (Σ t ꞉ (Σ P → Σ Q) , pr₁ ∘ t ∼ f ∘ pr₁) → Π (λ a → P a → Q (f a))
  ϕ (t , α) a u = transport Q (α (a , u)) (pr₂ (t (a , u)))
  
  ψ : Π (λ a → P a → Q (f a)) → (Σ t ꞉ (Σ P → Σ Q) , pr₁ ∘ t ∼ f ∘ pr₁)
  ψ g = total↓ Q f g , (hrefl _)
  
  ϕ∘ψ : ϕ ∘ ψ ∼ id
  ϕ∘ψ g = refl _

  ψ∘ϕ : ψ ∘ ϕ ∼ id
  ψ∘ϕ (f , α) = tot-≡ _ _ aux1 aux2
    where
    aux1 : pr₁ (ψ (ϕ (f , α))) ∼ f
    aux1 w = dpair-≡ ((α w ⁻¹) , (transport-∙ Q (α w) (α w ⁻¹) _ ∙ ap (λ - → transport Q - (pr₂ (f w))) (rinv (α w))))
    aux2 : hrefl _ ∼ (λ w → ap pr₁ (aux1 w) ∙ α w)
    aux2 w = linv _ ⁻¹ ∙ ((dpr₁-≡-β _ _) ⁻¹ ∙ᵣ _)

  equiv : (Σ t ꞉ (Σ P → Σ Q) , pr₁ ∘ t ∼ f ∘ pr₁) ≃ Π (λ a → P a → Q (f a))
  equiv = ϕ , qinv-to-isequiv (ψ , ϕ∘ψ , ψ∘ϕ)


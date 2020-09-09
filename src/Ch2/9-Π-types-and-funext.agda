{-# OPTIONS --without-K --exact-split --safe #-}

open import Ch1.Type-theory
open import Ch2.1-Types-are-higher-groupoids
open import Ch2.2-Functions-are-functors
open import Ch2.3-Type-families-are-fibrations
open import Ch2.4-Homotopies-and-equivalences
open import Ch2.7-Σ-types

module Ch2.9-Π-types-and-funext where


-- Function extensionality.

-- (i) From equality to homotopy

happly : {A : 𝓤 ̇} {B : A → 𝓥 ̇} {f g : Π B} → f ≡ g → f ∼ g
happly (refl f) x = refl (f x)


-- Pair of universes satisfies function extensionality

hfunext : (𝓤 𝓥 : Universe) → (𝓤 ⊔ 𝓥) ⁺ ̇
hfunext 𝓤 𝓥 = {A : 𝓤 ̇} {B : A → 𝓥 ̇} {f g : Π B} → isequiv (happly {𝓤} {𝓥} {A} {B} {f} {g})  

module hfunext {hfe : hfunext 𝓤 𝓥} {A : 𝓤 ̇} {B : A → 𝓥 ̇} {f g : Π B} where

  funext : f ∼ g → f ≡ g
  funext = qinv₁ (isequiv-to-qinv hfe)

  happly-β : happly ∘ funext ∼ 𝑖𝑑 (f ∼ g)
  happly-β = qinv₂ (isequiv-to-qinv hfe)

  happly-η : funext ∘ happly ∼ 𝑖𝑑 (f ≡ g)
  happly-η = qinv₃ (isequiv-to-qinv hfe)


-- (ii) Axiom 2.9.3 (Function Extensionality)

record FunExt : 𝓤ω where
  field
    happly-is-equiv : {𝓤 𝓥 : Universe} {A : 𝓤 ̇} {B : A → 𝓥 ̇} {f g : Π B} → isequiv (happly {𝓤} {𝓥} {A} {B} {f} {g}) 

open FunExt ⦃ ... ⦄ public


module _ ⦃ fe : FunExt ⦄ where 

  -- Quasi-inverse

  funext : {𝓤 𝓥 : Universe} {A : 𝓤 ̇} {B : A → 𝓥 ̇} {f g : Π B} → f ∼ g → f ≡ g
  funext = qinv₁ (isequiv-to-qinv happly-is-equiv)
  
  happly-β : {𝓤 𝓥 : Universe} {A : 𝓤 ̇} {B : A → 𝓥 ̇} {f g : Π B} (h : f ∼ g) → happly (funext h) ∼ h
  happly-β h = happly (qinv₂ (isequiv-to-qinv happly-is-equiv) h)

  happly-η : {𝓤 𝓥 : Universe} {A : 𝓤 ̇} {B : A → 𝓥 ̇} {f g : Π B} (p : f ≡ g) → funext (happly p) ≡ p
  happly-η = qinv₃ (isequiv-to-qinv happly-is-equiv)


  -- Pointwise characterization of refl, _⁻¹ and _∙_.

  fun-refl : {A : 𝓤 ̇} {B : A → 𝓥 ̇} (f : Π B) → refl f ≡ funext (hrefl f)
  fun-refl f = (happly-η (refl f)) ⁻¹

  fun-sym : {A : 𝓤 ̇} {B : A → 𝓥 ̇} {f g : Π B} (α : f ≡ g) → (α ⁻¹) ≡ funext (hsym (happly α))
  fun-sym (refl f) = fun-refl f

  fun-trans : {A : 𝓤 ̇} {B : A → 𝓥 ̇} {f g h : Π B} (α : f ≡ g) (β : g ≡ h) → (α ∙ β) ≡ funext (happly α · happly β)
  fun-trans (refl f) (refl f) = fun-refl f


-- Equation 2.9.4 (Transport of functions).

transport-fun : {X : 𝓤 ̇} {A : X → 𝓥 ̇} {B : X → 𝓦 ̇} {x₁ x₂ : X} (p : x₁ ≡ x₂) (f : A x₁ → B x₁) → transport (λ - → A - → B -) p f ∼ transport B p ∘ f ∘ transport A (p ⁻¹)
transport-fun (refl _) f a = refl (f a)


-- Equation 2.9.5 (Transport of dependent functions).

transport-dfun : {X : 𝓤 ̇} {A : X → 𝓥 ̇} {B : (x : X) → A x → 𝓥 ̇} {x₁ x₂ : X} (p : x₁ ≡ x₂) (f : (a : A x₁) → B x₁ a) → (a : A x₂) → transport (λ - → (a : A -) → B - a) p f a ≡ transport (Σ-induction B) (dpair-≡ ((p ⁻¹) , refl _) ⁻¹) (f (transport A (p ⁻¹) a))
transport-dfun (refl _) f a = refl (f a)


-- Lemma 2.9.6 (Function extensionality with respect to dependent paths; equality of parameterized functions). (TO DO: generalize to multiple universes)

module dpath-funext ⦃ fe : FunExt ⦄ {X : 𝓤 ̇} (A B : X → 𝓥 ̇) where

  P : X → 𝓥 ̇
  P x = A x → B x

  equiv :{x y : X} (p : x ≡ y) (f : P x) (g : P y) → (transport P p f ≡ g) ≃ ((a : A x) → transport B p (f a) ≡ g (transport A p a))
  equiv (refl _) f g = happly , happly-is-equiv 

  module paths {x y : X} (p : x ≡ y) (f : P x) (g : P y) (q : transport P p f ≡ g) (a : A x) where

    i : transport P p f (transport A p a) ≡ transport B p (f (transport A (p ⁻¹) (transport A p a)))
    i = transport-fun p f (transport A p a)

    j : transport B p (f (transport A (p ⁻¹) (transport A p a))) ≡ transport B p (f a)
    j = ap (transport B p ∘ f) (transport-∙ A p (p ⁻¹) a ∙ happly (ap (transport A) (rinv p)) a)
    
    k : transport B p (f a) ≡ g (transport A p a) 
    k = pr₁ (equiv p f g) q a
    
    ijk : transport P p f (transport A p a) ≡ g (transport A p a)
    ijk = i ∙ j ∙ k

  open paths

  dpath-funext-β : {x y : X} (p : x ≡ y) (f : P x) (g : P y) (q : transport P p f ≡ g) (a : A x) → happly q (transport A p a) ≡ ijk p f g q a
  dpath-funext-β (refl x) f g q a = lu _


-- Lemma 2.9.7 (Function extensionality with respect to dependent paths; equality of parameterized depedent functions). (TO DO: generalize to multiple universes)

module dpath-dfunext ⦃ fe : FunExt ⦄ {X : 𝓤 ̇} (A : X → 𝓥 ̇) (B : (x : X) → A x → 𝓥 ̇) where

  P : X → 𝓥 ̇
  P x = (a : A x) → B x a

  equiv : {x y : X} (p : x ≡ y) (f : P x) (g : P y) → (transport P p f ≡ g) ≃ ((a : A x) → transport (Σ-induction B) (dpair-≡ (p , refl _)) (f a) ≡ g (transport A p a))
  equiv (refl _) f g = happly , happly-is-equiv

  module paths where
  
    i : {x y : X} (p : x ≡ y) (f : P x) (g : P y) (q : transport P p f ≡ g) (a : A x) → transport P p f (transport A p a) ≡ transport (Σ-induction B) (dpair-≡ ((p ⁻¹) , refl _) ⁻¹) (f (transport A (p ⁻¹) (transport A p a)))
    i p f g q a = transport-dfun p f (transport A p a)

    j : {x y : X} (p : x ≡ y) (f : P x) (g : P y) (q : transport P p f ≡ g) (a : A x) → transport (Σ-induction B) (dpair-≡ ((p ⁻¹) , refl _) ⁻¹) (f (transport A (p ⁻¹) (transport A p a))) ≡ transport (Σ-induction B) (dpair-≡ (p , refl _)) (f a)
    j (refl _) f g q a = refl _

    k : {x y : X} (p : x ≡ y) (f : P x) (g : P y) (q : transport P p f ≡ g) (a : A x) → transport (Σ-induction B) (dpair-≡ (p , refl _)) (f a) ≡ g (transport A p a)
    k p f g = pr₁ (equiv p f g)

    ijk : {x y : X} (p : x ≡ y) (f : P x) (g : P y) (q : transport P p f ≡ g) (a : A x) → transport P p f (transport A p a) ≡ g (transport A p a)
    ijk p f g q a = i p f g q a ∙ j p f g q a ∙ k p f g q a

  open paths

  dpath-dfunext-β : {x y : X} (p : x ≡ y) (f : P x) (g : P y) (q : transport P p f ≡ g) (a : A x) → happly q (transport A p a) ≡ ijk p f g q a
  dpath-dfunext-β (refl _) f g q a = lu _


-- Particular case: dependent paths between homotopies. (TO DO: generalize to multiple universes)

module dpath-∼ ⦃ fe : FunExt ⦄ {A : 𝓤 ̇} {B : A → 𝓤 ̇} {g : Π B} (P : (f : Π B) → f ∼ g) where

  equiv : {f f' : Π B} (p : f ≡ f') (α : f ∼ g) (β : f' ∼ g) → (transport (_∼ g) p α ≡ β) ≃ ((a : A) → α a ≡ happly p a ∙ β a)
  equiv (refl _) α β = (happly , happly-is-equiv) ● (λ x a → x a ∙ lu _) , (qinv-to-isequiv ((λ x a → x a ∙ lu _ ⁻¹) , ((λ x → funext (λ a → ∙-assoc _ _ _ ⁻¹ ∙ (x a ∙ₗ linv _) ∙ ru _ ⁻¹)) , λ x → funext λ a → ∙-assoc _ _ _ ⁻¹ ∙ ((x a ∙ₗ rinv _) ∙ ru _ ⁻¹))))

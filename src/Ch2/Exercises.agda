{-# OPTIONS --without-K --exact-split --safe #-}

open import Ch1.Type-theory
open import Ch2.1-Types-are-higher-groupoids
open import Ch2.2-Functions-are-functors
open import Ch2.3-Type-families-are-fibrations 
open import Ch2.4-Homotopies-and-equivalences
open import Ch2.6-Cartesian-product-types
open import Ch2.7-Σ-types
open import Ch2.9-Π-types-and-funext
open import Ch2.10-Universes-and-univalence
open import Ch2.15-Universal-properties

module Ch2.Exercises where


-- Exercise 2.4 (n-dimensional paths in a type).

Bndry : ℕ → 𝓤 ̇ → 𝓤 ̇

Path : (n : ℕ) {A : 𝓤 ̇} → Bndry n A → 𝓤 ̇

Bndry {𝓤} zero A = Lift 𝓤 𝟙
Bndry (succ n) A = Σ b ꞉ Bndry n A , Path n b × Path n b

Path zero {A} b = A
Path (succ n) (b , lhs , rhs) = lhs ≡ rhs

lhs : {n : ℕ} {A : 𝓤 ̇} (b : Bndry (succ n) A) → Path n (pr₁ b)
lhs b = pr₁ (pr₂ b)

rhs : {n : ℕ} {A : 𝓤 ̇} (b : Bndry (succ n) A) → Path n (pr₁ b)
rhs b = pr₂ (pr₂ b)

module higher-paths where

  -- Action of a function on n-paths.

  ap'Codom : (n : ℕ) {A : 𝓤 ̇} {B : 𝓥 ̇} → (A → B) → (b : Bndry n A) → Path n b → 𝓥 ̇
  
  ap' : (n : ℕ) {A : 𝓤 ̇} {B : 𝓥 ̇} (f : A → B) {b : Bndry n A} (p : Path n b) → ap'Codom n f b p
  
  ap'Codom zero {A} {B} f b x = B
  ap'Codom (succ n) f (b , x , .x) (refl .x) = ap' n f x ≡ ap' n f x
  
  ap' zero f a = f a
  ap' (succ n) f (refl _) = refl (ap' n f _)

  -- ap' 1 is ap

  module _ (A : 𝓤 ̇) (B : 𝓥 ̇) (f : A → B) where 

    private
  
      type-agreement : (b : Bndry 1 A) (p : Path 1 b) → ap'Codom 1 f b p ≡ type-of (ap f p)
      type-agreement (b , x , .x) (refl .x) = refl _

      term-agreement : (b : Bndry 1 A) (p : Path 1 b) → coe (type-agreement b p) (ap' 1 f p) ≡ ap f p 
      term-agreement (b , x , .x) (refl .x) = refl _

  -- Dependent n-paths.

  BndryOver : (n : ℕ) {A : 𝓤 ̇} → (A → 𝓥 ̇) → Bndry n A → 𝓥 ̇

  PathOver' : (n : ℕ) {A : 𝓤 ̇} (P : A → 𝓥 ̇) {b : Bndry n A} → Path n b → BndryOver n P b → 𝓥 ̇

  BndryOver {𝓤} {𝓥} zero P b = Lift 𝓥 𝟙
  BndryOver (succ n) P (b , lhs , rhs) = Σ b' ꞉ BndryOver n P b , PathOver' n P lhs b' × PathOver' n P rhs b'
  
  PathOver' zero P x b' = P x
  PathOver' (succ n) P (refl _) (b' , lhs' , rhs') = lhs' ≡ rhs'


  -- Action of a dependent function on n-paths.

  apd'Codom : (n : ℕ) {A : 𝓤 ̇} {P : A → 𝓥 ̇} → Π P → (b : Bndry n A) → Path n b → 𝓥 ̇ 

  apd' : (n : ℕ) {A : 𝓤 ̇} {P : A → 𝓥 ̇} (f : Π P) {b : Bndry n A} (p : Path n b) → apd'Codom n f b p

  apd'Codom zero {A} {P} f b x = P x
  apd'Codom (succ n) f (b , x , .x) (refl .x) = apd' n f x ≡ apd' n f x 

  apd' zero f x = f x
  apd' (succ n) f (refl _) = refl (apd' n f _)

  -- apd' 1 is apd

  module _ {A : 𝓤 ̇} {P : A → 𝓥 ̇} (f : Π P) where

    private

      type-agreement : (b : Bndry 1 A) (p : Path 1 b) → apd'Codom 1 f b p ≡ type-of (apd f p) 
      type-agreement (b , x , .x) (refl .x) = refl _

      term-agreement : (b : Bndry 1 A) (p : Path 1 b) → coe (type-agreement b p) (apd' 1 f p) ≡ apd f p
      term-agreement (b , x , .x) (refl .x) = refl _
  
  -- Transport along n-paths. (Note: transport' is indexed by the dimension of the output.)

  left-basept : {n : ℕ} {A : 𝓤 ̇} → Bndry (succ n) A → A
  left-basept {n = zero} (b , lhs , rhs) = lhs
  left-basept {n = succ n} (b , lhs , rhs) = left-basept b

  transport'Codom : (n : ℕ) {A : 𝓤 ̇} (P : A → 𝓥 ̇) (b : Bndry (succ n) A) → Path (succ n) b → P (left-basept b) → 𝓥 ̇

  transport' : (n : ℕ) {A : 𝓤 ̇} (P : A → 𝓥 ̇) {b : Bndry (succ n) A} (p : Path (succ n) b) (u : P (left-basept b)) → transport'Codom n P b p u   

  transport'Codom zero P (b , x , .x) (refl .x) u = P x
  transport'Codom (succ n) P (b , x , .x) (refl .x) u = transport' n P x u ≡ transport' n P x u

  transport' zero P (refl x) = id
  transport' (succ n) P (refl x) u = refl _

  -- transport' 0 is transport

  module _ {A : 𝓤 ̇} (P : A → 𝓥 ̇) where

    private

      type-agreement : (b : Bndry 1 A) (p : Path 1 b) (u : P (left-basept b)) → transport'Codom 0 P b p u ≡ type-of (transport P p u)
      type-agreement (b , x , .x) (refl .x) u = refl _

      term-agreement : (b : Bndry 1 A) (p : Path 1 b) (u : P (left-basept b)) → coe (type-agreement b p u) (transport' 0 P p u) ≡ transport P p u 
      term-agreement (b , x , .x) (refl .x) u = refl _


-- Exercise 2.11 (Commutative square ; pullback square).

module pb-sq ⦃ fe : FunExt ⦄ {𝓤 𝓥 𝓦 : Universe} {A : 𝓤 ̇} {B : 𝓥 ̇} {C : 𝓦 ̇} (f : A → C) (g : B → C) where

  comm-sq : (P : 𝓣 ̇) → (𝓤 ⊔ 𝓥 ⊔ 𝓦 ⊔ 𝓣) ̇
  comm-sq P = Σ h ꞉ (P → A) , Σ k ꞉ (P → B) , f ∘ h ∼ g ∘ k

  pb-UMP : (X : 𝓣 ̇) → isequiv {_} {_} {X → pb f g} {comm-sq X} (λ u → pb₁ f g ∘ u , pb₂ f g ∘ u , pb-comm f g ∘ u)
  pb-UMP X = qinv-to-isequiv (
    (Σ-induction λ h → Σ-induction λ k α x → h x , k x , α x) ,
    (Σ-induction (λ h → Σ-induction λ k α → refl _)) ,
    λ u → refl _
    )
  


-- Exercise 2.10 (Dependent pairing is associative).

Σ-assoc : (A : 𝓤 ̇ ) (B : A → 𝓥 ̇ ) (C : Σ B → 𝓦 ̇ ) → (Σ (λ x → Σ (λ y → C (x , y)))) ≃ Σ C
Σ-assoc A B C = f , qinv-to-isequiv (g , (α , β))
 where
 f : Σ (λ x → Σ (λ y → C (x , y))) → Σ C
 f (x , (y , z)) = (x , y) , z
 g : Σ C → Σ (λ x → Σ (λ y → C (x , y)))
 g ((x , y) , z) = x , (y , z)
 α : (f ∘ g) ∼ id
 α ((x , y) , z) = refl _
 β : (g ∘ f) ∼ id
 β (x , (y , z)) = refl _

-- Related results: swapping independent components / arguments.

×-swap : (A : 𝓤 ̇) (B : 𝓥 ̇) → A × B ≃ B × A
×-swap A B = (Σ-induction λ a b → b , a) , (qinv-to-isequiv ((Σ-induction λ b a → a , b) , (λ x → refl _) , (λ x → refl _)))

Σ-swap : (A : 𝓤 ̇) (B : 𝓥 ̇) (C : A → B → 𝓦 ̇) → (Σ λ a → Σ λ b → C a b) ≃ (Σ λ b → Σ λ a → C a b)
Σ-swap A B C =
  (Σ-induction (λ a → Σ-induction λ b c → b , a , c)) ,
  (qinv-to-isequiv (
    Σ-induction (λ b → Σ-induction λ a c → a , b , c) ,
    refl ,
    refl 
  ))

Π-swap : (A : 𝓤 ̇) (B : 𝓥 ̇) (C : A → B → 𝓦 ̇) → ((a : A) (b : B) → C a b) ≃ ((b : B) (a : A) → C a b)
Π-swap A B C =
  swap ,
  (qinv-to-isequiv (
    swap ,
    refl ,
    refl
    ))


-- Exercise 2.17 (Type constructors preserve equivalences)

module _ ⦃ fe : FunExt ⦄ where

  -- (i) → preserves equivalences

  -- The proof of the following lemma does not require tools beyond Ch2, but the book does not use (nor prove) it until Ch4.

  -- Lemma 4.2.8.

  pre-∘-by-qinv-is-qinv : {A : 𝓤 ̇} {B : 𝓥 ̇} (C : 𝓦 ̇) (f : A → B) → qinv f → qinv (λ (h : B → C) → h ∘ f)
  pre-∘-by-qinv-is-qinv {A = A} {B} C f (g , β , α) =
    (λ h → h ∘ g) ,
    (λ h → funext λ a → ap h (α a)) ,
    λ h → funext (λ b → ap h (β b))

  post-∘-by-qinv-is-qinv : {A : 𝓤 ̇} {B : 𝓥 ̇} (C : 𝓦 ̇) (f : A → B) → qinv f → qinv (λ (h : C → A) → f ∘ h)
  post-∘-by-qinv-is-qinv {A = A} {B} C f (g , β , α) =
    (λ h → g ∘ h) ,
    (λ h → funext λ c → β (h c)) ,
    λ h → funext (λ c → α (h c))

  -- → preserves equivalence of domains

  →-preserves-dom-≃ : {A : 𝓤 ̇} {B : 𝓥 ̇} (C : 𝓦 ̇) → A ≃ B → (A → C) ≃ (B → C)
  →-preserves-dom-≃ C (f , i) = ≃-sym (_∘ f , qinv-to-isequiv (pre-∘-by-qinv-is-qinv C f (isequiv-to-qinv i)))

  -- → preserves equivalence of codomains

  →-preserves-codom-≃ : (A : 𝓤 ̇) {B : 𝓥 ̇} {C : 𝓦 ̇} → B ≃ C → (A → B) ≃ (A → C)
  →-preserves-codom-≃ A (f , i) = f ∘_ , qinv-to-isequiv (post-∘-by-qinv-is-qinv A f (isequiv-to-qinv i))

  -- Putting everything together:

  →-preserves-≃ : {A : 𝓤 ̇} {B : 𝓥 ̇} {C : 𝓥 ̇} {D : 𝓦 ̇} → A ≃ C → B ≃ D → (A → B) ≃ (C → D)
  →-preserves-≃ e₁ e₂ = →-preserves-dom-≃ _ e₁ ● →-preserves-codom-≃ _ e₂

  -- (ii) Π preserves equivalences

  private {- A more general version of the next result can be found in Ch4.2 -}

    module _ ⦃ univ : Univalence ⦄ where

      -- Π preserves equivalences of base types

      Π-preserves-base-≡ : {A B : 𝓤 ̇} (P : B → 𝓥 ̇) (p : A ≡ B) → Π (transport (λ - → - → 𝓥 ̇) (p ⁻¹) P) ≡ Π P
      Π-preserves-base-≡ P (refl A) = refl _ 

      Π-preserves-base-≃ : {A B : 𝓤 ̇} (P : B → 𝓥 ̇) → (e : A ≃ B) → Π (P ∘ (pr₁ e)) ≃ Π P
      Π-preserves-base-≃ {𝓤} {𝓥} {A} {B} P e = let p = ua e in idtoeqv (
        Π (P ∘ pr₁ e)
          ≡⟨ ap Π (funext (transport-along-ua-is-pre-∘ e P) ⁻¹) ⟩
        Π (transport (λ - → - → 𝓥 ̇) (p ⁻¹) P) 
          ≡⟨ Π-preserves-base-≡ P p ⟩
        Π P ∎
        )

      Π-preserves-base-≡' : {A B : 𝓤 ̇} (P : A → 𝓥 ̇) (p : A ≡ B) → Π P ≡ Π (transport (λ - → - → 𝓥 ̇) p P)
      Π-preserves-base-≡' P (refl A) = refl _ 

      Π-preserves-base-≃' : {A B : 𝓤 ̇} (P : A → 𝓥 ̇) → (e : A ≃ B) → Π P ≃ Π (P ∘ (inv e))
      Π-preserves-base-≃' {𝓤} {𝓥} {A} {B} P e = let p = ua e in idtoeqv (
        Π P
          ≡⟨ Π-preserves-base-≡' P p ⟩
        Π (transport (λ - → - → 𝓥 ̇) p P) 
          ≡⟨ ap Π (funext (transport-along-ua-is-pre-∘' e P)) ⟩
        Π (P ∘ (inv e))  ∎
        )

  -- Π preserves fiberwise equivalences

  Π-preserves-family-≃ : {A : 𝓤 ̇} {P : A → 𝓦 ̇} {Q : A → 𝓣 ̇} → ((a : A) → P a ≃ Q a) → Π P ≃ Π Q
  Π-preserves-family-≃ ϕ =
    (λ f a → F a (f a)) ,
    (qinv-to-isequiv (
      (λ g a → G a (g a)) ,
      (λ g → funext λ a → α a (g a)) ,
      λ f → funext λ a → β a (f a)
      )
    )
    where
    F = (λ a → pr₁ (ϕ a))
    q = (λ a → isequiv-to-qinv (pr₂ (ϕ a)))
    G = (λ a → qinv₁ (q a))
    α = (λ a → qinv₂ (q a))
    β = (λ a → qinv₃ (q a))

  -- (iii) Σ preserves equivalences

  private {- A more general version of the next result can be found in Ch4.2 -}

    module _ ⦃ univ : Univalence ⦄ where

      -- Σ preserves equivalences of base types

      Σ-preserves-base-≡ : {A B : 𝓤 ̇} (P : B → 𝓥 ̇) (p : A ≡ B) → Σ (transport (λ - → - → 𝓥 ̇) (p ⁻¹) P) ≡ Σ P
      Σ-preserves-base-≡ P (refl A) = refl _

      Σ-preserves-base-≃ : {A B : 𝓤 ̇} (P : B → 𝓥 ̇) (e : A ≃ B) → Σ (P ∘ (pr₁ e)) ≃ Σ P
      Σ-preserves-base-≃ {𝓤} {𝓥} {A} {B} P e = let p = ua e in idtoeqv
        (Σ (P ∘ pr₁ e)
          ≡⟨ ap Σ (funext (transport-along-ua-is-pre-∘ e P) ⁻¹) ⟩
        Σ (transport (λ - → - → 𝓥 ̇) (p ⁻¹) P)
          ≡⟨ Σ-preserves-base-≡ P p ⟩
        Σ P ∎
        )

      Σ-preserves-base-≡' : {A B : 𝓤 ̇} (P : A → 𝓥 ̇) (p : A ≡ B) → Σ P ≡ Σ (transport (λ - → - → 𝓥 ̇) p P)
      Σ-preserves-base-≡' P (refl A) = refl _

      Σ-preserves-base-≃' : {A B : 𝓤 ̇} (P : A → 𝓥 ̇) (e : A ≃ B) → Σ P ≃ Σ (P ∘ inv e)
      Σ-preserves-base-≃' {𝓤} {𝓥} {A} {B} P e = let p = ua e in idtoeqv
        (Σ P
          ≡⟨ Σ-preserves-base-≡' P p ⟩
        Σ (transport (λ - → - → 𝓥 ̇) p P)
          ≡⟨ ap Σ (funext (transport-along-ua-is-pre-∘' e P)) ⟩
        Σ (P ∘ inv e) ∎
        )

-- Σ preserves fiberwise equivalences

Σ-preserves-family-≡ : {A : 𝓤 ̇} {P Q : A → 𝓥 ̇} → (P ≡ Q) → Σ P ≡ Σ Q
Σ-preserves-family-≡ (refl P) = refl _

Σ-preserves-family-≃ : {A : 𝓤 ̇} {P : A → 𝓥 ̇} {Q : A → 𝓦 ̇} → ((a : A) → P a ≃ Q a) → Σ P ≃ Σ Q
Σ-preserves-family-≃ f =
  Σ-induction (λ a p → a , (pr₁ (f a) p)) ,
  (qinv-to-isequiv (
    Σ-induction (λ a q → a , (qinv₁ (isequiv-to-qinv (pr₂ (f a))) q)) ,
    Σ-induction (λ a q → dpair-≡ (refl a , (qinv₂ (isequiv-to-qinv (pr₂ (f a))) q))) ,
    Σ-induction (λ a p → dpair-≡ ((refl a) , ((qinv₃ (isequiv-to-qinv (pr₂ (f a))) p))))
    )
  )

-- (iv) × preserves equivalences

×-preserves-≃ : {A : 𝓤 ̇} {B : 𝓥 ̇} {C : 𝓥 ̇} {D : 𝓦 ̇} → A ≃ C → B ≃ D → A × B ≃ C × D
×-preserves-≃ (f , i) (g , j) with isequiv-to-qinv i | isequiv-to-qinv j
... | (finv , α , β) | (ginv , γ , δ) = (Σ-induction λ a b → (f a , g b)) , qinv-to-isequiv ((Σ-induction λ c d → (finv c , ginv d)) , (Σ-induction λ c d → pair-≡ (α c , γ d)) , (Σ-induction λ a b → pair-≡ (β a , δ b)))

-- (v) + preserves equivalences

+-preserves-≃ : {A : 𝓤 ̇} {B : 𝓥 ̇} {C : 𝓥 ̇} {D : 𝓦 ̇} → A ≃ C → B ≃ D → A + B ≃ C + D
+-preserves-≃ (f , i) (g , j) with isequiv-to-qinv i | isequiv-to-qinv j
... | (finv , α , β) | (ginv , γ , δ) = +-recursion (inl ∘ f) (inr ∘ g) , qinv-to-isequiv (+-recursion (inl ∘ finv) (inr ∘ ginv) , +-induction _ (λ c → ap inl (α c)) (λ d → ap inr (γ d)) , +-induction _ (λ a → ap inl (β a)) (λ b → ap inr (δ b)))


private {- The following results are experimental / exploratory. -}

  module whiskering-and-hz-composition where


    -- (i) Whiskering


    -- Alternative definition of whiskering operations

    ∙ᵣ-agrees-with-ap : {A : 𝓤 ̇ } {a b c : A} {p q : a ≡ b} (α : p ≡ q) (r : b ≡ c) → α ∙ᵣ r ≡ ap (_∙ r) α
    ∙ᵣ-agrees-with-ap {𝓤} {A} {.b} {.b} {.b} {.(refl b)} {.(refl b)} (refl (refl .b)) (refl b) = refl _

    ∙ₗ-agrees-with-ap : {A : 𝓤 ̇ } {a b c : A} {r s : b ≡ c} (q : a ≡ b) (β : r ≡ s) → q ∙ₗ β ≡ ap (q ∙_) β 
    ∙ₗ-agrees-with-ap {𝓤} {A} {.b} {.b} {.b} {.(refl b)} {.(refl b)} (refl b) (refl (refl .b)) = refl _


    -- Iterated whiskering (particular case of associativity of _⋆'_)

    iterated-∙ᵣ-is-∙ : {A : 𝓤 ̇ } {a b c d : A} {p q : a ≡ b} (α : p ≡ q) (r : b ≡ c) (s : c ≡ d)  → (α ∙ᵣ r) ∙ᵣ s ≡ (∙-assoc _ _ _ ⁻¹) ∙ (α ∙ᵣ (r ∙ s)) ∙ (∙-assoc _ _ _)
    iterated-∙ᵣ-is-∙ (refl (refl .x)) (refl .x) (refl x) = refl _

    iterated-∙ₗ-is-∙ : {A : 𝓤 ̇ } {a b c d : A} {r s : c ≡ d} (p : a ≡ b) (q : b ≡ c) (β : r ≡ s) → p ∙ₗ (q ∙ₗ β) ≡ (∙-assoc _ _ _) ∙ ((p ∙ q) ∙ₗ β) ∙ (∙-assoc _ _ _ ⁻¹)
    iterated-∙ₗ-is-∙ (refl .x) (refl x) (refl (refl .x)) = refl _


    -- Unit laws for whiskering (particular case of identity of _⋆'_)

    ∙ᵣ-ru : {A : 𝓤 ̇} {a b : A} {p q : a ≡ b} (α : p ≡ q) → ru p ⁻¹ ∙ α ∙ ru q  ≡ α ∙ᵣ refl b   
    ∙ᵣ-ru (refl (refl x)) = refl _

    ∙ₗ-lu : {A : 𝓤 ̇} {a b : A} {p q : a ≡ b} (α : p ≡ q) → lu p ⁻¹ ∙ α ∙ lu q ≡ refl a ∙ₗ α   
    ∙ₗ-lu (refl (refl x)) = refl _


    -- (ii) Horizontal composition


    -- Associativity of horizontal composition

    ⋆'-assoc : {A : 𝓤 ̇ } {a b c d : A} {p q : a ≡ b} {r s : b ≡ c} {t u : c ≡ d} (α : p ≡ q) (β : r ≡ s) (γ : t ≡ u) → α ⋆' (β ⋆' γ) ≡ ∙-assoc p r t ∙ ((α ⋆' β) ⋆' γ) ∙ (∙-assoc q s u ⁻¹)
    ⋆'-assoc (refl (refl .x)) (refl (refl .x)) (refl (refl x)) = refl _


    -- Unit laws for horizontal composition

    ⋆'-ru : {A : 𝓤 ̇ } {a b c : A} {p q : a ≡ b} (α : p ≡ q) → α ≡ ru p ∙ (α ⋆' refl (refl b)) ∙ ru q ⁻¹
    ⋆'-ru (refl (refl x)) = refl _


    -- Horizontal inverse

    ⋆'-sym : {A : 𝓤 ̇ } {a b : A} {p q : a ≡ b} → p ≡ q →  p ⁻¹ ≡ q ⁻¹
    ⋆'-sym {p = refl x} (refl .(refl x)) = refl _


    -- Inverse law

    ⋆'-rinv : {A : 𝓤 ̇ } {a b : A} {p q : a ≡ b} (α : p ≡ q) →  α ⋆' (⋆'-sym α) ≡ rinv p ∙ refl (refl a) ∙ (rinv q ⁻¹)
    ⋆'-rinv {p = .(refl x)} (refl (refl x)) = refl _


    -- Whiskering is horizontal composition with refl

    ⋆'-refl-is-∙ᵣ : {A : 𝓤 ̇ } {a b c : A} {p q : a ≡ b} (α : p ≡ q) (r : b ≡ c) → α ⋆' (refl r) ≡ α ∙ᵣ r 
    ⋆'-refl-is-∙ᵣ (refl (refl .x)) (refl x) = refl _

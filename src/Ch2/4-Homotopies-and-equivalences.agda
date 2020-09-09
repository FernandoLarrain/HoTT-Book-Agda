{-# OPTIONS --without-K --exact-split --safe #-}

open import Ch1.Type-theory
open import Ch2.1-Types-are-higher-groupoids
open import Ch2.2-Functions-are-functors
open import Ch2.3-Type-families-are-fibrations

module Ch2.4-Homotopies-and-equivalences where


-- Definition 2.4.1 (Homotopy).

_∼_ : {A : 𝓤 ̇} {P : A → 𝓥 ̇} → Π P → Π P → 𝓤 ⊔ 𝓥 ̇
f ∼ g = ∀ x → f x ≡ g x

infix 0 _∼_


-- Lemma 2.4.2 (Homotopy is an equivalence relation).

module _ {A : 𝓤 ̇} {P : A → 𝓥 ̇} where 

  hrefl : (f : Π P) → f ∼ f
  hrefl f x = refl (f x)

  hsym : {f g : Π P} → f ∼ g → g ∼ f
  hsym H x = H x ⁻¹

  _·_ : {f g h : Π P} → f ∼ g → g ∼ h → f ∼ h
  _·_ F G x = F x ∙ G x

  infixl 30 _·_


-- Equational reasoning with _·_

module _ {A : 𝓤 ̇} {P : A → 𝓥 ̇} where

  _∼⟨_⟩_ : (f : Π P) {g h : Π P} → f ∼ g → g ∼ h → f ∼ h
  _ ∼⟨ α ⟩ β = α · β

  infixr 0 _∼⟨_⟩_

  _□ : (f : Π P) → f ∼ f
  _□ = hrefl

  infix 1 _□ 


-- Groupoid laws for homotopies

module _ {A : 𝓤 ̇} {P : A → 𝓥 ̇} {f g : Π P} where

  ∼-ru : (α : f ∼ g) → α · hrefl g ∼ α
  ∼-ru α x = ru _ ⁻¹ 

  ∼-lu : (α : f ∼ g) → hrefl f · α ∼ α 
  ∼-lu α x = lu _ ⁻¹

  ∼-rinv : (α : f ∼ g) → α · hsym α ∼ hrefl f
  ∼-rinv α x = rinv _ 

  ∼-linv : (α : f ∼ g) → hsym α · α ∼ hrefl g
  ∼-linv α x = linv _

  hsym-invol : (α : f ∼ g) → hsym (hsym α) ∼ α
  hsym-invol α x = ⁻¹-invol _

·-assoc : {A : 𝓤 ̇} {P : A → 𝓥 ̇} {f g h k : Π P} (α : f ∼ g) (β : g ∼ h) (γ : h ∼ k) → α · (β · γ) ∼ α · β · γ
·-assoc α β γ x = ∙-assoc _ _ _

-- A related law

∼-distr : {A : 𝓤 ̇} {P : A → 𝓥 ̇} {f g h : Π P} (α : f ∼ g) (β : g ∼ h) → hsym (α · β) ∼ hsym β · hsym α
∼-distr α β x = distr _ _


-- Homotopy whiskering operations

_·ᵣ_ : {A : 𝓤 ̇} {B : 𝓥 ̇} {C : 𝓦 ̇} {f g : A → B} → f ∼ g → (h : B → C) → h ∘ f ∼ h ∘ g
(α ·ᵣ h) x = ap h (α x)

infix 30 _·ᵣ_

_·ₗ_ : {A : 𝓤 ̇} {B : 𝓥 ̇} {C : 𝓦 ̇} {g h : B → C} (f : A → B) → g ∼ h → g ∘ f ∼ h ∘ f
(f ·ₗ α) = α ∘ f

infix 30 _·ₗ_


-- Lemma 2.4.3 (Naturality of homotopies).

module _ {A : 𝓤 ̇} {B : 𝓥 ̇} {f g : A → B} {x y : A} (H : f ∼ g) where

  hnat : (p : x ≡ y) → H x ∙ ap g p ≡ ap f p ∙ H y
  hnat (refl _) = ru _ ⁻¹ ∙ lu _

  hnat' : (p : x ≡ y) → H x ⁻¹ ∙ ap f p ∙ H y ≡ ap g p
  hnat' (refl _) = ap (_∙ H _) (ru _ ⁻¹) ∙ linv _

  hnat'' : (p : x ≡ y) → ap f p ⁻¹ ∙ H x ∙ ap g p  ≡ H y
  hnat'' (refl _) = ru _ ⁻¹ ∙ lu _ ⁻¹


-- Corollary 2.4.4.

hnat-id : {A : 𝓤 ̇} {f : A → A} (H : f ∼ id) (x : A) → H (f x) ≡ ap f (H x)
hnat-id {𝓤} {A} {f} H x =
  H (f x)
    ≡⟨ ru _ ∙ ap (H (f x) ∙_) (rinv (H x) ⁻¹) ⟩ 
  H (f x) ∙ (H x ∙ (H x ⁻¹))
    ≡⟨ ∙-assoc _ _ _ ⟩ 
  H (f x) ∙ H x ∙ H x ⁻¹
    ≡⟨ ap (_∙ (H x ⁻¹)) (ap (H (f x) ∙_) (ap-id (H x) ⁻¹) ∙ hnat H (H x)) ⟩
  ap f (H x) ∙ H x ∙ H x ⁻¹
    ≡⟨ ∙-assoc _ _ _ ⁻¹ ⟩ 
  ap f (H x) ∙ (H x ∙ (H x ⁻¹))
    ≡⟨ (ru _ ∙ ap (ap f (H x) ∙_) (rinv (H x) ⁻¹)) ⁻¹ ⟩
   ap f (H x)
  ∎


-- Example: Lift is a functor

Lift-map : (𝓥 : Universe) {X Y : 𝓤 ̇} → (X → Y) → Lift 𝓥 X → Lift 𝓥 Y
Lift-map 𝓥 f = lift ∘ Lift-recursion 𝓥 f

Lift-id : (𝓥 : Universe) (X : 𝓤 ̇) → Lift-map 𝓥 (𝑖𝑑 X) ∼ 𝑖𝑑 (Lift 𝓥 X)
Lift-id 𝓥 X = hrefl _

Lift-∘ : (𝓥 : Universe) {X Y Z : 𝓤 ̇} (f : X → Y) (g : Y → Z) → Lift-map 𝓥 (g ∘ f) ∼ Lift-map 𝓥 g ∘ Lift-map 𝓥 f
Lift-∘ 𝓥 f g = hrefl _


-- Definition 2.4.6 (Quasi-inverse).

module _ {A : 𝓤 ̇} {B : 𝓥 ̇} where 

  qinv : (f : A → B) → 𝓤 ⊔ 𝓥 ̇
  qinv f = Σ g ꞉ (B → A) , (f ∘ g ∼ id) × (g ∘ f ∼ id)

  qinv₁ : {f : A → B} → qinv f → B → A
  qinv₁ (g , α , β) = g 

  qinv₂ : {f : A → B} → (q : qinv f) → (f ∘ qinv₁ q ∼ id)
  qinv₂ (g , α , β) = α 

  qinv₃ : {f : A → B} → (q : qinv f) → (qinv₁ q ∘ f ∼ id)
  qinv₃ (g , α , β) = β 


-- Example 2.4.7 (Identity is its own quasi-inverse).

qinv-𝑖𝑑 : (A : 𝓤 ̇) → qinv (𝑖𝑑 A)
qinv-𝑖𝑑 A = 𝑖𝑑 A , refl , refl


-- Example 2.4.8 (Pre- and post-concatenation are quasi-invertible).

qinv-pre-∙ : {A : 𝓤 ̇} {x y : A} (z : A) (p : x ≡ y) → qinv (λ (q : y ≡ z) → p ∙ q)
qinv-pre-∙ {𝓤} {A} {x} {y} z p =
  (p ⁻¹ ∙_) ,
  (λ r → ∙-assoc _ _ _ ∙ (ap (_∙ r) (rinv p) ∙ lu _ ⁻¹)) ,
  λ r → ∙-assoc _ _ _ ∙ (ap (_∙ r) (linv p) ∙ lu _ ⁻¹)

qinv-post-∙ : {A : 𝓤 ̇} {x y : A} (z : A) (p : x ≡ y)  → qinv (λ (q : z ≡ x) → q ∙ p)
qinv-post-∙ {𝓤} {A} {x} {y} z p =
  (_∙ p ⁻¹) ,
  (λ r → ∙-assoc _ _ _ ⁻¹ ∙ (ap (r ∙_) (linv p) ∙ ru _ ⁻¹)) ,
  λ r → ∙-assoc _ _ _ ⁻¹ ∙ (ap (r ∙_) (rinv p) ∙ ru _ ⁻¹)


-- Example: _⁻¹ is its own quasi-inverse

qinv-⁻¹ : {A : 𝓤 ̇} (x y : A) → qinv (_⁻¹ {𝓤} {A} {x} {y})
qinv-⁻¹ x y =
  _⁻¹ ,
  ⁻¹-invol ,
  ⁻¹-invol


-- Example : whiskering operations have quasi-inverses

module _ {A : 𝓤 ̇} {a b c : A} where

  -- _∙ₗ_ has qinv (for each left argument)

  ∙ₗ-inv : (q : a ≡ b) (r s : b ≡ c) → q ∙ r ≡ q ∙ s → r ≡ s
  ∙ₗ-inv (refl b) r s β = lu r ∙ β ∙ lu s ⁻¹ 

  ∙ₗ-inv-is-linv : (q : a ≡ b) (r s : b ≡ c) → ∙ₗ-inv q r s ∘ (q ∙ₗ_) ∼ id
  ∙ₗ-inv-is-linv (refl .x) (refl x) .(refl x) (refl .(refl x)) = refl _

  ∙ₗ-inv-is-rinv : (q : a ≡ b) (r s : b ≡ c) → (q ∙ₗ_) ∘ ∙ₗ-inv q r s  ∼ id
  ∙ₗ-inv-is-rinv (refl x) r (refl .x) β = ru _ ⁻¹ ∙ ∙-assoc _ _ _ ∙ ru _ ⁻¹ ∙ ∙-assoc _ _ _ ∙ (linv _ ∙ᵣ β) ∙ lu _ ⁻¹

  qinv-∙ₗ : (q : a ≡ b) (r s : b ≡ c) → qinv (q ∙ₗ_)
  qinv-∙ₗ q r s = ∙ₗ-inv q r s , ∙ₗ-inv-is-rinv q r s , ∙ₗ-inv-is-linv q r s

  -- _∙ᵣ_ has qinv (for each right argument)

  ∙ᵣ-inv : (p q : a ≡ b) (r : b ≡ c) → p ∙ r ≡ q ∙ r → p ≡ q
  ∙ᵣ-inv p q (refl b) α = ru p ∙ α ∙ ru q ⁻¹

  ∙ᵣ-inv-is-linv : (p q : a ≡ b) (r : b ≡ c) → ∙ᵣ-inv p q r ∘ (_∙ᵣ r) ∼ id
  ∙ᵣ-inv-is-linv (refl x) .(refl x) (refl .x) (refl .(refl x)) = refl _

  ∙ᵣ-inv-is-rinv : (p q : a ≡ b) (r : b ≡ c) → (_∙ᵣ r) ∘ ∙ᵣ-inv p q r  ∼ id
  ∙ᵣ-inv-is-rinv p (refl .x) (refl x) α = ru _ ⁻¹ ∙ ∙-assoc _ _ _ ∙ ru _ ⁻¹ ∙ ∙-assoc _ _ _ ∙ (linv _ ∙ᵣ α) ∙ lu _ ⁻¹

  qinv-∙ᵣ : (p q : a ≡ b) (r : b ≡ c) → qinv (_∙ᵣ r)
  qinv-∙ᵣ p q r = ∙ᵣ-inv p q r , ∙ᵣ-inv-is-rinv p q r , ∙ᵣ-inv-is-linv p q r


-- Example 2.4.9

qinv-transport : {A : 𝓤 ̇} (P : A → 𝓥 ̇) {x y : A} (p : x ≡ y) → qinv (transport P p)
qinv-transport P p =
  (transport P (p ⁻¹)) ,
  (λ v → transport-∙ P (p ⁻¹) p v ∙ ap (λ w → transport P w v) (linv p)) ,
  λ u → transport-∙ P p (p ⁻¹) u ∙ ap (λ w → transport P w u) (rinv p)


-- Example: lift and lower are quasi-invertible.

qinv-lift : {𝓥 : Universe} {A : 𝓤 ̇} → qinv (lift {𝓤} {𝓥} {A})
qinv-lift {𝓤} {𝓥} {A} = lower , hrefl _ , hrefl _

qinv-lower : {𝓥 : Universe} {A : 𝓤 ̇} → qinv (lower {𝓤} {𝓥} {A})
qinv-lower {𝓤} {𝓥} {A} = lift , hrefl _ , hrefl _


-- I. Old definition of equivalence (used up to Ch4.5).

module old-equiv where

  module _ {A : 𝓤 ̇} {B : 𝓥 ̇} where

    -- Equation 2.4.10 (Is equivalence).

    isequiv : (f : A → B) → 𝓤 ⊔ 𝓥 ̇
    isequiv f = (Σ g ꞉ (B → A) , (f ∘ g ∼ id)) × (Σ h ꞉ (B → A) , (h ∘ f ∼ id))

    isequiv₁ : {f : A → B} → isequiv f → B → A
    isequiv₁ ((g , α) , (h , β)) = g

    isequiv₂ : {f : A → B} → (e : isequiv f) → (f ∘ isequiv₁ e ∼ id)
    isequiv₂ ((g , α) , (h , β)) = α

    isequiv₃ : {f : A → B} → isequiv f → B → A
    isequiv₃ ((g , α) , (h , β)) = h

    isequiv₄ : {f : A → B} → (e : isequiv f) → (isequiv₃ e ∘ f ∼ id)
    isequiv₄ ((g , α) , (h , β)) = β

    -- Page 78, (i) From qinv to isequiv

    qinv-to-isequiv : {f : A → B} → qinv f → isequiv f
    qinv-to-isequiv (g , α , β) = (g , α) , (g , β)


    -- Page 78, (ii) From isequiv to qinv

    isequiv-to-qinv : {f : A → B} → isequiv f → qinv f
    isequiv-to-qinv {f} ((g , α) , (h , β)) =
      g ,
      α ,
      λ x → hsym β (g (f x)) ∙ (ap h (α (f x)) ∙ β x)  


  -- Equation 2.4.11 (Equivalence).

  _≃_ : 𝓤 ̇ → 𝓥 ̇ → 𝓤 ⊔ 𝓥 ̇
  A ≃ B = Σ f ꞉ (A → B) , isequiv f

  infix 10 _≃_

  inv : {A : 𝓤 ̇} {B : 𝓥 ̇} (e : A ≃ B) → B → A
  inv (f , (g , α) , (h , β)) = g


  -- Lemma 2.4.12 (≃ is an equivalence relation).

  ≃-refl : (A : 𝓤 ̇) → A ≃ A
  ≃-refl A = 𝑖𝑑 A , qinv-to-isequiv (qinv-𝑖𝑑 A)

  ≃-sym : {A : 𝓤 ̇} {B : 𝓥 ̇} → (A ≃ B) → (B ≃ A)
  ≃-sym {𝓤} {𝓥} {A} {B} (f , e) = let q = isequiv-to-qinv e in qinv₁ q , qinv-to-isequiv (f , (qinv₃ q) , (qinv₂ q))

  _●_ : {A : 𝓤 ̇} {B : 𝓥 ̇} {C : 𝓦 ̇} → (A ≃ B) → (B ≃ C) → (A ≃ C)
  f , (g , α) , (h , β) ● f' , (g' , α') , (h' , β') =
    f' ∘ f ,
    (g ∘ g' , λ c → ap f' (α _) ∙ α' _) ,
    (h ∘ h' , λ a → ap h (β' _) ∙ β _)

  infixl 30 _●_  


  -- Equational reasoning with _≃_

  _≃⟨_⟩_ : (X : 𝓤 ̇) {Y : 𝓥 ̇} {Z : 𝓦 ̇} → X ≃ Y → Y ≃ Z → X ≃ Z
  _ ≃⟨ d ⟩ e = d ● e

  infixr 0 _≃⟨_⟩_

  _■ : (X : 𝓤 ̇) → X ≃ X
  _■ = ≃-refl

  infix 1 _■ 


-- II. New defintion of equivalence (used in Ch4.5 onwards). 

module new-equiv where

  module _ {A : 𝓤 ̇} {B : 𝓥 ̇} where

    -- Definition (Is equivalence). (Def. 4.2.1) 

    isequiv : (f : A → B) → 𝓤 ⊔ 𝓥 ̇
    isequiv f = Σ g ꞉ (B → A) , Σ η ꞉ g ∘ f ∼ id , Σ ε ꞉ f ∘ g ∼ id , ((x : A) → ap f (η x) ≡ ε (f x))

    isequiv₁ : {f : A → B} → isequiv f → B → A
    isequiv₁ (g , η , ε , τ) = g

    isequiv₂ : {f : A → B} → (h : isequiv f) → isequiv₁ h ∘ f ∼ id
    isequiv₂ (g , η , ε , τ) = η

    isequiv₃ : {f : A → B} → (h : isequiv f) → f ∘ isequiv₁ h ∼ id
    isequiv₃ (g , η , ε , τ) = ε

    isequiv₄ : {f : A → B} → (h : isequiv f) → (x : A) → ap f (isequiv₂ h x) ≡ isequiv₃ h (f x)
    isequiv₄ (g , η , ε , τ) = τ
    

    -- From qinv to isequiv. (Thm. 4.2.3)

    qinv-to-isequiv : {f : A → B} → qinv f → isequiv f
    qinv-to-isequiv {f} (g , ε , η) =
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


    -- From isequiv to qinv. (Thm. 4.2.3)

    isequiv-to-qinv : {f : A → B} → isequiv f → qinv f
    isequiv-to-qinv (g , η , ε , τ) = (g , ε , η)


  -- Equation 2.4.11 (Equivalence).

  _≃_ : 𝓤 ̇ → 𝓥 ̇ → 𝓤 ⊔ 𝓥 ̇
  A ≃ B = Σ f ꞉ (A → B) , isequiv f

  infix 10 _≃_

  inv : {A : 𝓤 ̇} {B : 𝓥 ̇} (e : A ≃ B) → B → A
  inv (f , g , η , ε , τ) = g


  -- Lemma 2.4.12 (≃ is an equivalence relation).

  ≃-refl : (A : 𝓤 ̇) → A ≃ A
  ≃-refl A = 𝑖𝑑 A , qinv-to-isequiv (qinv-𝑖𝑑 A)

  ≃-sym : {A : 𝓤 ̇} {B : 𝓥 ̇} → (A ≃ B) → (B ≃ A)
  ≃-sym {𝓤} {𝓥} {A} {B} (f , e) = qinv₁ q , qinv-to-isequiv (f , (qinv₃ q) , (qinv₂ q))
    where
    q = isequiv-to-qinv e

  _●_ : {A : 𝓤 ̇} {B : 𝓥 ̇} {C : 𝓦 ̇} → (A ≃ B) → (B ≃ C) → (A ≃ C)
  _●_ (f , e) (f' , e') with isequiv-to-qinv e | isequiv-to-qinv e'
  ... | (g , α , β) | (g' , α' , β')  = f' ∘ f , qinv-to-isequiv ((g ∘ g') , ((λ b → ap f'(α _) ∙ α' _) , (λ a → ap g (β' _) ∙ β _)))

  infixl 30 _●_


  -- Equational reasoning with _≃_.

  _≃⟨_⟩_ : (X : 𝓤 ̇) {Y : 𝓥 ̇} {Z : 𝓦 ̇} → X ≃ Y → Y ≃ Z → X ≃ Z
  _ ≃⟨ d ⟩ e = d ● e

  infixr 0 _≃⟨_⟩_

  _■ : (X : 𝓤 ̇) → X ≃ X
  _■ = ≃-refl

  infix 1 _■ 

open new-equiv public


-- We can translate all previous examples of quasi-invertible maps to equivalences:

-- Example 2.4.8 (Pre- and post-concatenation are equivalences).

pre-∙-≃ : {A : 𝓤 ̇} {x y : A} (z : A) → x ≡ y → (y ≡ z) ≃ (x ≡ z)
pre-∙-≃ z p = (p ∙_) , qinv-to-isequiv (qinv-pre-∙ _ _)

post-∙-≃ : {A : 𝓤 ̇} {x y : A} (z : A) → x ≡ y → (z ≡ x) ≃ (z ≡ y)
post-∙-≃ z p = (_∙ p) , qinv-to-isequiv (qinv-post-∙ _ _)

-- Example: _⁻¹ is an equivalence.

⁻¹-≃ : {A : 𝓤 ̇} (x y : A) → (x ≡ y) ≃ (y ≡ x)
⁻¹-≃ x y = _⁻¹ , qinv-to-isequiv (qinv-⁻¹ _ _)

-- Example : whiskering operations induce equivalences

module _ {A : 𝓤 ̇} {a b c : A} where

  -- _∙ₗ_ is an equivalence (for each left argument)

  ∙ₗ-≃ : (q : a ≡ b) (r s : b ≡ c) → (q ∙ r ≡ q ∙ s) ≃ (r ≡ s) 
  ∙ₗ-≃ q r s = ≃-sym ((q ∙ₗ_) , qinv-to-isequiv (qinv-∙ₗ _ _ _))
  
  -- _∙ᵣ_ is an equivalence (for each right argument)

  ∙ᵣ-≃ : (p q : a ≡ b) (r : b ≡ c) → (p ∙ r ≡ q ∙ r) ≃ (p ≡ q)
  ∙ᵣ-≃ p q r = ≃-sym ((_∙ᵣ r) , qinv-to-isequiv (qinv-∙ᵣ _ _ _))

-- Example 2.4.9

transport-≃ : {A : 𝓤 ̇} (P : A → 𝓥 ̇) {x y : A} → x ≡ y → P x ≃ P y
transport-≃ P p = transport P p , qinv-to-isequiv (qinv-transport P p)

-- Example: lift and lower are equivalences (i.e. types are equivalent to their lifts).

Lift-≃ : {𝓥 : Universe} {A : 𝓤 ̇} → Lift 𝓥 A ≃ A
Lift-≃ {𝓤} {𝓥} {A} = lower , qinv-to-isequiv qinv-lower 

≃-Lift : {𝓥 : Universe} {A : 𝓤 ̇} → A ≃ Lift 𝓥 A
≃-Lift {𝓤} {𝓥} {A} = lift , qinv-to-isequiv qinv-lift

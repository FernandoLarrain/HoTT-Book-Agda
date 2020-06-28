{-# OPTIONS --without-K --exact-split --safe #-}

open import Ch1.Type-theory
open import Ch2.1-Types-are-higher-groupoids
open import Ch2.2-Functions-are-functors
open import Ch2.3-Type-families-are-fibrations

module Ch2.4-Homotopies-and-equivalences-new where


-- Definition 2.4.1 (Homotopy).

_∼_ : {A : 𝓤 ̇ } {P : A → 𝓥 ̇ } → Π P → Π P → 𝓤 ⊔ 𝓥 ̇
f ∼ g = ∀ x → f x ≡ g x

infix 0 _∼_


-- Lemma 2.4.2 (Homotopy is an equivalence relation).

hrefl : {A : 𝓤 ̇ } {P : A → 𝓥 ̇ } (f : Π P) → f ∼ f
hrefl f x = refl (f x)

hsym : {A : 𝓤 ̇ } {P : A → 𝓥 ̇ } {f g : Π P} → f ∼ g → g ∼ f
hsym H x = H x ⁻¹

htrans : {A : 𝓤 ̇ } {P : A → 𝓥 ̇ } {f g h : Π P} → f ∼ g → g ∼ h → f ∼ h
htrans F G x = F x ∙ G x


-- Lemma 2.4.3 (Naturality of homotopies).

hnat : {A : 𝓤 ̇ } {B : 𝓥 ̇ } {f g : A → B} {x y : A} (H : f ∼ g) (p : x ≡ y) → H x ∙ ap g p ≡ ap f p ∙ H y
hnat {f = f} {g} H (refl x) =
  H x ∙ ap g (refl x)
    ≡⟨ ru _ ⁻¹ ⟩
  H x
    ≡⟨ lu _ ⟩
  ap f (refl x) ∙ H x
  ∎

hnat' : {A : 𝓤 ̇ } {B : 𝓥 ̇ } {f g : A → B} {x y : A} (H : f ∼ g) (p : x ≡ y) → H x ⁻¹ ∙ ap f p ∙ H y ≡ ap g p
hnat' H (refl x) = ap (_∙ H x) (ru _ ⁻¹) ∙ linv _

hnat'' : {A : 𝓤 ̇ } {B : 𝓥 ̇ } {f g : A → B} {x y : A} (H : f ∼ g) (p : x ≡ y) → ap f p ⁻¹ ∙ H x ∙ ap g p  ≡ H y
hnat'' H (refl x) = ru _ ⁻¹ ∙ lu _ ⁻¹


-- Corollary 2.4.4.

hnat-id : {A : 𝓤 ̇ } {f : A → A} (H : f ∼ id) (x : A) → H (f x) ≡ ap f (H x)
hnat-id {f = f} H x =
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
  

-- Definition 2.4.6 (Quasi-inverse).

qinv : {A : 𝓤 ̇ } {B : 𝓥 ̇ } (f : A → B) → 𝓤 ⊔ 𝓥 ̇
qinv {A = A} {B = B} f = Σ g ꞉ (B → A) , (f ∘ g ∼ id) × (g ∘ f ∼ id)

qinv₁ : {A : 𝓤 ̇ } {B : 𝓥 ̇ } {f : A → B} → qinv f → B → A
qinv₁ (g , α , β) = g 

qinv₂ : {A : 𝓤 ̇ } {B : 𝓥 ̇ } {f : A → B} → (q : qinv f) → (f ∘ qinv₁ q ∼ id)
qinv₂ (g , α , β) = α 

qinv₃ : {A : 𝓤 ̇ } {B : 𝓥 ̇ } {f : A → B} → (q : qinv f) → (qinv₁ q ∘ f ∼ id)
qinv₃ (g , α , β) = β 


-- Example 2.4.7 (Identity has a quasi-inverse).

qinv-𝑖𝑑 : (A : 𝓤 ̇ ) → qinv (𝑖𝑑 A)
qinv-𝑖𝑑 A = 𝑖𝑑 A , refl , refl


-- Example 2.4.8 (Pre- and post-concatenation are quasi-invertible).

qinv-pre-∙ : {A : 𝓤 ̇ } {x y : A} (z : A) (p : x ≡ y) → qinv (λ (q : y ≡ z) → p ∙ q)
qinv-pre-∙ {x = x} {y = y} z p =
  (p ⁻¹ ∙_) ,
  (λ x₁ → ∙-assoc _ _ _ ∙ (ap (_∙ x₁) (rinv p) ∙ lu _ ⁻¹)) ,
  λ x₁ → ∙-assoc _ _ _ ∙ (ap (_∙ x₁) (linv p) ∙ lu _ ⁻¹)

qinv-post-∙ : {A : 𝓤 ̇ } {x y : A} (z : A) (p : x ≡ y)  → qinv (λ (q : z ≡ x) → q ∙ p)
qinv-post-∙ {x = x} {y = y} z p =
  (_∙ p ⁻¹) ,
  (λ x₁ → ∙-assoc _ _ _ ⁻¹ ∙ (ap (x₁ ∙_) (linv p) ∙ ru _ ⁻¹)) ,
  λ x₁ → ∙-assoc _ _ _ ⁻¹ ∙ (ap (x₁ ∙_) (rinv p) ∙ ru _ ⁻¹)


-- _⁻¹ is its own quasi-inverse

qinv-⁻¹ : {A : 𝓤 ̇} (x y : A) → qinv (_⁻¹ {x = x} {y})
qinv-⁻¹ x y =
  _⁻¹ ,
  ⁻¹-invol ,
  ⁻¹-invol


-- _∙ₗ_ has qinv (for each left argument)

∙ₗ-inv : {A : 𝓤 ̇} {a b c : A} (q : a ≡ b) (r s : b ≡ c) → q ∙ r ≡ q ∙ s → r ≡ s
∙ₗ-inv (refl b) r s β' = lu r ∙ β' ∙ lu s ⁻¹ 

∙ₗ-inv-is-linv : {A : 𝓤 ̇} {a b c : A} (q : a ≡ b) (r s : b ≡ c) → ∙ₗ-inv q r s ∘ (q ∙ₗ_) ∼ id
∙ₗ-inv-is-linv {A = A} {.x} {.x} {.x} (refl .x) (refl x) .(refl x) (refl .(refl x)) = refl _
  
∙ₗ-inv-is-rinv : {A : 𝓤 ̇} {a b c : A} (q : a ≡ b) (r s : b ≡ c) → (q ∙ₗ_) ∘ ∙ₗ-inv q r s  ∼ id
∙ₗ-inv-is-rinv (refl x) r (refl .x) β rewrite ru (lu r ∙ β) ⁻¹ | ru (lu r ⁻¹ ∙ (lu r ∙ β)) ⁻¹ | ∙-assoc (lu r ⁻¹) (lu r) β | linv (lu r) | lu r ⁻¹ | lu β ⁻¹ = refl _

qinv-∙ₗ : {A : 𝓤 ̇} {a b c : A} (q : a ≡ b) (r s : b ≡ c) → qinv (q ∙ₗ_)
qinv-∙ₗ q r s = ∙ₗ-inv q r s , ∙ₗ-inv-is-rinv q r s , ∙ₗ-inv-is-linv q r s


-- _∙ᵣ_ has qinv (for each right argument)

∙ᵣ-inv : {A : 𝓤 ̇} {a b c : A} (p q : a ≡ b) (r : b ≡ c) → p ∙ r ≡ q ∙ r → p ≡ q
∙ᵣ-inv p q (refl b) α' = ru p ∙ α' ∙ ru q ⁻¹

∙ᵣ-inv-is-linv : {A : 𝓤 ̇} {a b c : A} (p q : a ≡ b) (r : b ≡ c) → ∙ᵣ-inv p q r ∘ (_∙ᵣ r) ∼ id
∙ᵣ-inv-is-linv {A = A} {.x} {.x} {.x} (refl x) .(refl x) (refl .x) (refl .(refl x)) = refl _
  
∙ᵣ-inv-is-rinv : {A : 𝓤 ̇} {a b c : A} (p q : a ≡ b) (r : b ≡ c) → (_∙ᵣ r) ∘ ∙ᵣ-inv p q r  ∼ id
∙ᵣ-inv-is-rinv p (refl .x) (refl x) α' rewrite ru (ru p ∙ α') ⁻¹ | ru (ru p ⁻¹ ∙ (ru p ∙ α')) ⁻¹ | ∙-assoc (ru p ⁻¹) (ru p) α' | ap (_∙ α') (linv (ru p)) | lu α' ⁻¹ = refl _

qinv-∙ᵣ : {A : 𝓤 ̇} {a b c : A} (p q : a ≡ b) (r : b ≡ c) → qinv (_∙ᵣ r)
qinv-∙ᵣ p q r = ∙ᵣ-inv p q r , ∙ᵣ-inv-is-rinv p q r , ∙ᵣ-inv-is-linv p q r


-- Example 2.4.9

qinv-transport : {A : 𝓤 ̇} (P : A → 𝓥 ̇) {x y : A} (p : x ≡ y) → qinv (transport P p)
qinv-transport P p =
  (transport P (p ⁻¹)) ,
  (λ v → transport-∙ P (p ⁻¹) p v ∙ ap (λ w → transport P w v) (linv p)) ,
  λ u → transport-∙ P p (p ⁻¹) u ∙ ap (λ w → transport P w u) (rinv p)


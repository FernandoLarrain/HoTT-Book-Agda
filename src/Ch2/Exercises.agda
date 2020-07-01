{-# OPTIONS --without-K --exact-split #-}

open import Ch1.Type-theory
open import Ch2.1-Types-are-higher-groupoids
open import Ch2.2-Functions-are-functors
open import Ch2.3-Type-families-are-fibrations 
open import Ch2.4-Homotopies-and-equivalences
open import Ch2.7-Σ-types
open import Ch2.9-Π-types-and-funext
open import Ch2.10-Universes-and-univalence

module Ch2.Exercises where


-- Exercise 2.4 (n-dimensional paths in a type).

Bndry : ℕ → 𝓤 ̇ → 𝓤 ̇

Path : (n : ℕ) {A : 𝓤 ̇} → Bndry n A → 𝓤 ̇

Bndry {𝓤} zero A = Lift 𝓤 𝟙
Bndry (succ n) A = Σ b ꞉ Bndry n A , Path n b × Path n b

Path zero {A} b = A -- Maybe substitute ∂ for b?
Path (succ n) (b , lhs , rhs) = lhs ≡ rhs

{- Old definitions:
 
Path : ℕ → 𝓤 ̇ → 𝓤 ̇
Path zero A = A
Path (succ n) A = Σ w ꞉ (Path n A × Path n A)  , pr₁ w ≡ pr₂ w

lhs : (n : ℕ) (A : 𝓤 ̇) → Path (succ n) A → Path n A
lhs n A ((a , b) , p) = a

rhs : (n : ℕ) (A : 𝓤 ̇) → Path (succ n) A → Path n A
rhs n A ((a , b) , p) = b

path : (n : ℕ) (A : 𝓤 ̇) → (z : Path (succ n) A) → lhs n A z ≡ rhs n A z
path n A ((a , b) , p) = p

boundary : (n : ℕ) (A : 𝓤 ̇) → Path (succ n) A → Path n A × Path n A
boundary n A ((a , b) , p) = a , b

-}

module higher-paths where

  -- Action of a function on n-paths.

  ap'Codom : (n : ℕ) {A : 𝓤 ̇} {B : 𝓥 ̇} (f : A → B) {b : Bndry n A} (p : Path n b) → 𝓥 ̇
  
  ap' : (n : ℕ) {A : 𝓤 ̇} {B : 𝓥 ̇} (f : A → B) {b : Bndry n A} (p : Path n b) → ap'Codom n f p
  
  ap'Codom zero {A} {B} f a = B
  ap'Codom (succ n) f (refl x) = ap' n f x ≡ ap' n f x
  
  ap' zero f a = f a
  ap' (succ n) f (refl _) = refl (ap' n f _)

  -- Dependent n-paths.

  BndryOver : (n : ℕ) {A : 𝓤 ̇} → (A → 𝓥 ̇) → Bndry n A → 𝓥 ̇

  PathOver' : (n : ℕ) {A : 𝓤 ̇} (P : A → 𝓥 ̇) {b : Bndry n A} (p : Path n b) (b' : BndryOver n P b) → 𝓥 ̇

  BndryOver {𝓤} {𝓥} zero P b = Lift 𝓥 𝟙
  BndryOver (succ n) P (b , lhs , rhs) = Σ b' ꞉ BndryOver n P b , PathOver' n P lhs b' × PathOver' n P rhs b'
  
  PathOver' zero P a b' = P a
  PathOver' (succ n) P (refl _) (b' , lhs' , rhs') = lhs' ≡ rhs'

  -- Action of a dependent function on n-paths.

  apd'Codom : (n : ℕ) {A : 𝓤 ̇} {P : A → 𝓥 ̇} (f : Π P) {b : Bndry n A} (p : Path n b) → 𝓥 ̇ 

  apd' : (n : ℕ) {A : 𝓤 ̇} {P : A → 𝓥 ̇} (f : Π P) {b : Bndry n A} (p : Path n b) → apd'Codom n f p

  apd'Codom zero {A} {P} f a = P a
  apd'Codom (succ n) f (refl x) = apd' n f x ≡ apd' n f x 

  apd' zero f a = f a
  apd' (succ n) f (refl _) = refl _
  
  -- Transport along n-paths. (Note: transport' is indexed by the dimension of the output.)

  left-basept : {n : ℕ} {A : 𝓤 ̇} → Bndry (succ n) A → A
  left-basept {n = zero} (b , lhs , rhs) = lhs
  left-basept {n = succ n} (b , lhs , rhs) = left-basept b

  transport'Codom : (n : ℕ) {A : 𝓤 ̇} (P : A → 𝓥 ̇) (b : Bndry (succ n) A) → Path (succ n) b → P (left-basept b) → 𝓥 ̇

  transport' : (n : ℕ) {A : 𝓤 ̇} (P : A → 𝓥 ̇) (b : Bndry (succ n) A) (p : Path (succ n) b) (u : P (left-basept b)) → transport'Codom n P b p u   

  transport'Codom zero P (x , a , .a) (refl .a) u = P a
  transport'Codom (succ n) P (b , lhs , .lhs) (refl .lhs) u = transport' n P b lhs u ≡ transport' n P b lhs u

  transport' zero P (x , a , .a) (refl .a) = id
  transport' (succ n) P (b , lhs , .lhs) (refl .lhs) u = refl _

  {- Old definitions:

  -- Action of a function on n-paths.

  ApCodomain : (n : ℕ) {A : 𝓤 ̇} {B : 𝓥 ̇} (f : A → B) (z : Path n A) → 𝓥 ̇
  Ap : (n : ℕ) {A : 𝓤 ̇} {B : 𝓥 ̇} (f : A → B) (z : Path n A) → ApCodomain n f z
  ApCodomain  zero {B = B} f a = B
  ApCodomain (succ n) f ((a , .a) , refl .a) = Ap n f a ≡ Ap n f a
  Ap zero f a = f a
  Ap (succ n) f ((a , .a) , refl .a) = refl (Ap n f a)


  -- Transport along n-dimensional paths.

  lbasept : (n : ℕ) (A : 𝓤 ̇) → Path (succ n) A → A
  lbasept (zero) A ((a , b) , p) = a
  lbasept (succ n) A ((a , b) , p) = lbasept n A a

  rbasept : (n : ℕ) (A : 𝓤 ̇) → Path (succ n) A → A
  rbasept (zero) A ((a , b) , p) = b
  rbasept (succ n) A ((a , b) , p) = rbasept n A b

  TransportCodomain : (n : ℕ) {A : 𝓤 ̇} (P : A → 𝓥 ̇) (z : Path (succ n) A) (u : P (lbasept n A z)) → 𝓥 ̇
  Transport : (n : ℕ) {A : 𝓤 ̇} (P : A → 𝓥 ̇) (z : Path (succ n) A) (u : P (lbasept n A z)) → TransportCodomain n P z u
  TransportCodomain zero P ((x , y) , p) u = P y
  TransportCodomain (succ n) P ((x , .x) , refl .x) u = Transport n P x u ≡ Transport n P x u
  Transport zero P ((x , .x) , refl .x) = 𝑖𝑑 (P x)
  Transport (succ n) P ((x , .x) , refl .x) u = refl (Transport n P x u)

  -- Dependent n-paths.

  DepPath : (n : ℕ) {A : 𝓤 ̇} (P : A → 𝓥 ̇) (z : Path n A) → 𝓥 ̇
  DepPath zero P x = Path zero (P x)
  DepPath (succ n) P ((x , .x) , refl .x) = Path (succ n) (DepPath n P x)

  -- Dependent action on n-paths.

  ApdCodomain : (n : ℕ) {A : 𝓤 ̇} {P : A → 𝓥 ̇} (f : Π P) (z : Path n A) → 𝓥 ̇
  Apd : (n : ℕ) {A : 𝓤 ̇} {P : A → 𝓥 ̇} (f : Π P) (z : Path n A) → ApdCodomain n f z
  ApdCodomain zero {P = P} f a = P a
  ApdCodomain (succ n) {P = P} f ((x , .x) , refl .x) = Apd n f x ≡ Apd n f x 
  Apd zero f a = f a
  Apd (succ n) f ((x , .x) , refl .x) = refl (Apd n f x)

  -}

  -- TO DO: check definitions, prove that they coincide with the definitions in the book, see if they are related to one another (e.g. dependent case over constant family, transport and dependent paths) and apply to loop spaces and n-spheres (exercise 6.4).


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

-- Related results: swapping independent arguments / components.

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
  (λ f b a → f a b) ,
  (qinv-to-isequiv (
    (λ g a b → g b a) ,
    refl ,
    refl
    ))


-- Exercise 2.17 (Type constructors preserve equivalences)

-- (i) Σ preserves equivalences
  
Σ-preserves-family-≃ : {A : 𝓤 ̇} {P : A → 𝓥 ̇} {Q : A → 𝓦 ̇} → ((a : A) → P a ≃ Q a) → Σ P ≃ Σ Q
Σ-preserves-family-≃ f =
  Σ-induction (λ a p → a , (pr₁ (f a) p)) ,
  (qinv-to-isequiv (
    Σ-induction (λ a q → a , (qinv₁ (isequiv-to-qinv (pr₂ (f a))) q)) ,
    Σ-induction (λ a q → dpair-≡ (refl a , (qinv₂ (isequiv-to-qinv (pr₂ (f a))) q))) ,
    Σ-induction (λ a p → dpair-≡ ((refl a) , ((qinv₃ (isequiv-to-qinv (pr₂ (f a))) p))))
    )
  )

-- (ii) Π preserves equivalences

Π-preserves-family-≃ : {A : 𝓤 ̇} {P : A → 𝓦 ̇} {Q : A → 𝓣 ̇} → ((a : A) → P a ≃ Q a) → Π P ≃ Π Q
Π-preserves-family-≃ ϕ =
  (λ f a → F a (f a)) ,
  (qinv-to-isequiv (
    (λ g a → G a (g a)) ,
    (λ g → funext _ _ λ a → α a (g a)) ,
    λ f → funext _ _ λ a → β a (f a)
    )
  )
  where
  F = (λ a → pr₁ (ϕ a))
  q = (λ a → isequiv-to-qinv (pr₂ (ϕ a)))
  G = (λ a → qinv₁ (q a))
  α = (λ a → qinv₂ (q a))
  β = (λ a → qinv₃ (q a))


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

  ⋆'-sym : {A : 𝓤 ̇ } {a b : A} {p q : a ≡ b} (α : p ≡ q) →  p ⁻¹ ≡ q ⁻¹
  ⋆'-sym {p = refl x} (refl .(refl x)) = refl _


  -- Inverse law

  ⋆'-rinv : {A : 𝓤 ̇ } {a b : A} {p q : a ≡ b} (α : p ≡ q) →  α ⋆' (⋆'-sym α) ≡ rinv p ∙ refl (refl a) ∙ (rinv q ⁻¹)
  ⋆'-rinv {p = .(refl x)} (refl (refl x)) = refl _


  -- Whiskering is horizontal composition with refl

  ⋆'-refl-is-∙ᵣ : {A : 𝓤 ̇ } {a b c : A} {p q : a ≡ b} (α : p ≡ q) (r : b ≡ c) → α ⋆' (refl r) ≡ α ∙ᵣ r 
  ⋆'-refl-is-∙ᵣ (refl (refl .x)) (refl x) = refl _



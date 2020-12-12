{-# OPTIONS --without-K --exact-split #-}

open import Ch1.Type-theory
open import Ch2.Homotopy-type-theory
open import Ch3.Sets-and-logic
open import Ch4.Equivalences
open import Ch6.9-Truncations
open import Ch7.1-Definition-of-n-types
open import Ch7.3-Truncations-safe

module Ch7.5-Connectedness ⦃ tc : Truncations ⦄ where


-- Definition 7.5.1 (n-connected types and functions).

is_connected_ : Tlevel → 𝓤 ̇ → 𝓤 ̇
is n connected A = isContr (∥ A ∥ n)

≃-preserves-is-conn : (n : Tlevel) {A : 𝓤 ̇} {B : 𝓥 ̇} → A ≃ B → is n connected A → is n connected B
≃-preserves-is-conn n e = ≃-preserves-Contr (∥∥-preserves-≃ e)

conn : Tlevel → {A : 𝓤 ̇} {B : 𝓥 ̇} → (A → B) → 𝓤 ⊔ 𝓥 ̇
conn n {A} {B} f = (b : B) → is n connected (fib f b)

is-conn-⇔-conn-!𝟙 : (n : Tlevel) (A : 𝓤 ̇) → is n connected A ⇔ conn n (!𝟙 A)
is-conn-⇔-conn-!𝟙 n A = (λ A-is-conn → 𝟙-induction _ (≃-preserves-is-conn n (≃-sym fib-of-!𝟙) A-is-conn)) , (λ !𝟙-is-conn → ≃-preserves-is-conn n fib-of-!𝟙 (!𝟙-is-conn ⋆))

is-conn-is-Prop : (n : Tlevel) (A : 𝓤 ̇) → isProp (is n connected A)
is-conn-is-Prop n A = isContr-is-Prop _

conn-is-Prop : (n : Tlevel) {A : 𝓤 ̇} {B : 𝓥 ̇} (f : A → B) → isProp (conn n f)
conn-is-Prop n f = Π-preserves-Props _ λ b → isContr-is-Prop _

is-conn-≃-conn-!𝟙 : (n : Tlevel) (A : 𝓤 ̇) → is n connected A ≃ conn n (!𝟙 A)
is-conn-≃-conn-!𝟙 n A = ⇔-to-≃ (is-conn-is-Prop n A) (conn-is-Prop n (!𝟙 A)) (is-conn-⇔-conn-!𝟙 n A) 

is-conn-preserves-≃ : (n : Tlevel) {A : 𝓤 ̇} {B : 𝓥 ̇} → A ≃ B → is n connected A ≃ is n connected B
is-conn-preserves-≃ n {A} {B} e = ⇔-to-≃ (is-conn-is-Prop n A) (is-conn-is-Prop n B) (≃-preserves-is-conn n e , ≃-preserves-is-conn n (≃-sym e))


-- Lemma 7.5.2. (f is -1-connected iff it is surjective).

conn-⟨-1⟩-≃-isSurjective : {A : 𝓤 ̇} {B : 𝓥 ̇} (f : A → B) → conn ⟨-1⟩ f ≃ isSurjective f
conn-⟨-1⟩-≃-isSurjective f = Π-preserves-family-≃ (λ b → ⇔-to-≃ (isContr-is-Prop _) ∃-is-Prop (isProp-to-isContr-iff-is-inhabited ∃-is-Prop))


-- Definition (Connected , simply connected).

isConn : 𝓤 ̇ → 𝓤 ̇
isConn A = is ⟨0⟩ connected A

isSimplyConn : 𝓤 ̇ → 𝓤 ̇
isSimplyConn A = is ⟨1⟩ connected A


-- Lemma 7.5.4 (Retractions of maps preserve connectedness).

retractions-of-maps-preserve-conn : (n : Tlevel) {A : 𝓤 ̇} {B : 𝓥 ̇} {X : 𝓦 ̇} {Y : 𝓣 ̇} {g : A → B} {f : X → Y} → g is-retract-of f → conn n f → conn n g
retractions-of-maps-preserve-conn n ρ i b = retract-of-Contr-is-Contr (∥∥-preserves-◁ (retraction-of-maps-to-fiberwise-retraction ρ b)) (i _)


-- Corollary 7.5.5 (Homotopy preserves connectedness).

∼-preserves-conn : (n : Tlevel) {A : 𝓤 ̇} {B : 𝓥 ̇} {f g : A → B} → f ∼ g → conn n f → conn n g
∼-preserves-conn n = retractions-of-maps-preserve-conn n ∘ ∼-to-retract


-- Lemma 7.5.6.

conn-∘ : (n : Tlevel) {A : 𝓤 ̇} {B : 𝓥 ̇} {C : 𝓦 ̇} {f : A → B} (g : B → C) → conn n f → conn n g ⇔ conn n (g ∘ f)
conn-∘ n {A} {B} {C} {f} g f-is-conn = (λ f-is-conn c → ≃-preserves-Contr (≃-sym (aux-≃ c)) (f-is-conn c)) , λ ∘-is-conn c → ≃-preserves-Contr (aux-≃ c) (∘-is-conn c) where
  aux-≃ : (c : C) → (∥ fib (g ∘ f) c ∥ n) ≃ (∥ fib g c ∥ n)
  aux-≃ c =
    (∥ fib (g ∘ f) c ∥ n)
      ≃⟨ ∥∥-preserves-≃ (fib-∘ f g c) ⟩
    ∥ Σ w ꞉ fib g c , fib f (pr₁ w) ∥ n
      ≃⟨ ≃-sym ∥∥-preserves-Σ.equiv ⟩
    ∥ Σ w ꞉ fib g c , ∥ fib f (pr₁ w) ∥ n ∥ n
      ≃⟨ ∥∥-preserves-≃ (Σ-of-Contr-family-is-base _ _ (f-is-conn ∘ pr₁)) ⟩
    (∥ fib g c ∥ n) ■


-- Lemma 7.5.7 (Induction principle of n-connected maps).

module conn-induction (n : Tlevel) {A : 𝓤 ̇} {B : 𝓥 ̇} (f : A → B) where

  pre-∘ : (P : B → n Type 𝓦) → Π (pr₁ ∘ P) → Π (pr₁ ∘ P ∘ f)
  pre-∘ P = _∘ f

  -- TFAE

  i : 𝓤 ⊔ 𝓥 ̇
  i = conn n f
  
  ii : 𝓤 ⊔ 𝓥 ⊔ (𝓦 ⁺) ̇
  ii {𝓦} = (P : B → n Type 𝓦) → isequiv (pre-∘ P)
  
  iii : 𝓤 ⊔ 𝓥 ⊔ (𝓦 ⁺) ̇
  iii {𝓦} = (P : B → n Type 𝓦) → sec (pre-∘ P)

  -- Statements i and ii are propositions

  i-is-Prop : isProp i
  i-is-Prop = conn-is-Prop n f

  ii-is-Prop : isProp (ii {𝓦})
  ii-is-Prop = Π-preserves-Props _ (λ P → ishae-is-Prop _)

  -- Proof

  i-to-ii : i → ii {𝓦}
  i-to-ii f-is-conn P = transport isequiv (funext underlying-fun-∼) (pr₂ aux-equiv) where
    aux-equiv : Π (pr₁ ∘ P) ≃ Π (pr₁ ∘ P ∘ f)
    aux-equiv =
      Π (pr₁ ∘ P)
        ≃⟨ Π-preserves-family-≃ (λ b → pts-of-type.equiv (pr₁ (P b)) (f-is-conn b)) ⟩
      ((b : B) → ∥ fib f b ∥ n → pr₁ (P b))
        ≃⟨ Π-preserves-family-≃ (λ b → ∥∥-UMP.equiv n (fib f b) (pr₂ (P b))) ⟩
      ((b : B) → fib f b → pr₁ (P b))
        ≃⟨ Π-preserves-family-≃ (λ b → GCCAdj _ _ _) ⟩
      ((b : B) (a : A) (p : f a ≡ b) → pr₁ (P b))
        ≃⟨ (Π-swap _ _ _) ● (Π-preserves-family-≃ (λ a → ≃-sym (GCCAdj _ _ _))) ⟩
      ((a : A) (w : Σ b ꞉ B , f a ≡ b) → pr₁ (P (pr₁ w)))
        ≃⟨ Π-preserves-family-≃ (λ a → Π-over-Contr-base-is-fib _ _ (free-right-endpt-is-Contr _ _)) ⟩
      Π (pr₁ ∘ P ∘ f) ■
    underlying-fun-∼ : pr₁ aux-equiv ∼ pre-∘ P
    underlying-fun-∼ s = funext (λ a → (transportconst (pr₁ (P (f a))) (pr₂ (f-is-conn (f a)) ∣ (a , refl (f a)) ∣) (s (f a))))


  ii-to-iii : ii {𝓦} → iii {𝓦}
  ii-to-iii equiv P with equiv P
  ... | (g , η , ε , τ) = g , ε


  iii-to-i : iii {𝓤 ⊔ 𝓥} → i
  iii-to-i section = pair (c , suffices (happly c-β)) where
    P : B → n Type (𝓤 ⊔ 𝓥)
    P b = (∥ fib f b ∥ n) , ∥∥-Tlevel
    c : Π (pr₁ ∘ P)
    c = pr₁ (section P) (λ a →  ∣ a , refl (f a) ∣)
    c-β : c ∘ f ≡ λ a → ∣ a , refl (f a) ∣
    c-β = (pr₂ (section P) (λ a → ∣ a , refl (f a) ∣))
    suffices : (c ∘ f ∼ λ a → ∣ a , refl (f a) ∣) → ((b : B) (w : ∥ fib f b ∥ n) → c b ≡ w)
    suffices c-β b = ∥∥-induction (λ x → Tlevel-is-cumulative ∥∥-Tlevel _ _) (Σ-induction (λ a → ℍ (f a) (λ b p → c b ≡ ∣ a , p ∣) (c-β a) b))

  -- Logical equivalences

  ii-to-i : ii {𝓤 ⊔ 𝓥} → i
  ii-to-i = iii-to-i ∘ ii-to-iii

  i-iff-ii : i ⇔ ii {𝓤 ⊔ 𝓥}
  i-iff-ii = i-to-ii , ii-to-i

  i-to-iii : i → iii {𝓦}
  i-to-iii = ii-to-iii ∘ i-to-ii

  i-iff-iii : i ⇔ iii {𝓤 ⊔ 𝓥}
  i-iff-iii = i-to-iii {𝓤 ⊔ 𝓥} , iii-to-i

  iii-to-ii : iii {𝓤 ⊔ 𝓥} → ii {𝓤 ⊔ 𝓥}
  iii-to-ii = i-to-ii ∘ iii-to-i

  ii-iff-iii : ii ⇔ iii
  ii-iff-iii = ii-to-iii , iii-to-ii

  -- Equivalences

  i-≃-ii : i ≃ ii {𝓤 ⊔ 𝓥}
  i-≃-ii = ⇔-to-≃ i-is-Prop ii-is-Prop i-iff-ii

  -- Convenient reformulation of main results:

  -- n-connected map induction (i-to-iii)

  conn-induction : conn n f → {P : B → 𝓦 ̇} → ((b : B) → is n type (P b)) → Π (P ∘ f) → Π P
  conn-induction c {P} i = pr₁ (i-to-iii c (λ b → P b , i b))

  pre-∘-β : (c : conn n f) {P : B → 𝓦 ̇} (i : (b : B) → is n type (P b)) (g : Π (P ∘ f)) → conn-induction c i g ∘ f ≡ g
  pre-∘-β c {P} i = pr₂ (i-to-iii c (λ b → P b , i b))

  -- n-connectedness criterion for functions (iii-to-i)

  conn-criterion : ({P : B → 𝓤 ⊔ 𝓥 ̇} (i : (b : B) → is n type (P b)) → sec (λ (s' : Π P) → s' ∘ f)) → conn n f  
  conn-criterion section = iii-to-i (λ P → section (λ b → pr₂ (P b)))

open conn-induction using (conn-induction ; conn-criterion) renaming (i-≃-ii to conn-induction-≃) public


-- Corollary 7.5.8 (∣_∣ is n-connected).

conn-∣∣ : {n : Tlevel} {A : 𝓤 ̇} → conn n {A} {∥ A ∥ n} ∣_∣
conn-∣∣ {𝓤} {n} {A} = conn-criterion n ∣_∣ λ i → ∥∥-induction i , λ s' → funext (∣∣-prop-β i s')


-- TO DO

-- -- Corollary 7.5.9 (A type A is n-connected iff every map from A to an n-type is constant).

-- is-conn-≃-constant-maps : {n : Tlevel} {A : 𝓤 ̇} → is n connected A ≃ ((B : 𝓤 ⊔ 𝓥 ̇) → is n type B → isequiv (λ (b : B) (a : A) → b))
-- is-conn-≃-constant-maps {𝓤} {𝓥} {n} {A} = {!!} -- ⇔-to-≃ (is-conn-is-Prop _ _) (Π-preserves-Props _ (λ B → →-preserves-Props _ _ (ishae-is-Prop _))) {!!}

-- {- is n connected A ≃ conn n !𝟙 A ≃ ((P : 𝟙 → n Type 𝓤 ⊔ 𝓥) ...  -}


-- -- Lemma 7.5.10.

-- isequiv-iff-conn : {n : Tlevel} {A : 𝓤 ̇} {B : 𝓥 ̇} (i : is n type B) (f : A → B) → isequiv f ⇔ conn n (∥∥-recursion i f)
-- isequiv-iff-conn {𝓤} {𝓥} {n} {A} {B} i f = {!conn-∘ n g conn-∣∣ !} where
--   g : ∥ A ∥ n → B
--   g = ∥∥-recursion i f
--   fun-≡ : f ≡ g ∘ ∣_∣
--   fun-≡ = ∥∥-UMP.β n A i f ⁻¹
  
  






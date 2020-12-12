{-# OPTIONS --without-K --exact-split #-}

open import Ch1.Type-theory
open import Ch2.Homotopy-type-theory
open import Ch3.1-Sets-and-n-types
open import Ch3.3-Mere-propositions

module Ch3.5-Subsets-and-prop-resizing where


-- Lemma 3.5.1 (Irrelevance of propositional information).

-- Note: "predicates" or "properties" are just families of propositions. Arbitrary families are called "data".

Σ-over-predicate : {A : 𝓤 ̇} {P : A → 𝓥 ̇} → ((x : A) → isProp (P x)) → {u v : Σ P} → pr₁ u ≡ pr₁ v → u ≡ v
Σ-over-predicate f {u} {v} p = dpair-≡ (p , (f (pr₁ v) _ _))

Σ-over-predicate' : {A : 𝓤 ̇} {P : A → 𝓥 ̇} → ((x : A) → isProp (P x)) → (u v : Σ P) → (u ≡ v) ≃ (pr₁ u ≡ pr₁ v) 
Σ-over-predicate' {𝓤} {𝓥} {A} {P} f u v =
  let f' : (x : A) → isSet (P x)
      f' x = isProp-to-isSet (f x)
  in ap pr₁ ,
     qinv-to-isequiv (
       (λ p → dpair-≡ (p , (f (pr₁ v) _ (pr₂ v))) ) ,
       (λ p → dpr₁-≡-β p (f (pr₁ v) _ (pr₂ v))) ,
       λ q → ap dpair-≡ (dpair-≡ ((refl _) , f' _ _ _ _ _)) ∙ dpr-≡-η' q
      )


-- Definitions (subuniverses of propositions and sets).

-- Prop and Set are keywords

PROP : (𝓤 : Universe) → 𝓤 ⁺ ̇
PROP 𝓤  = Σ A ꞉ 𝓤 ̇ , isProp A 

SET : (𝓤 : Universe) → 𝓤 ⁺ ̇
SET 𝓤 = Σ A ꞉ 𝓤 ̇ , isSet A


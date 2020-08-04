{-# OPTIONS --without-K --exact-split --safe #-}

open import Ch1.Type-theory
open import Ch2.Homotopy-type-theory
open import Ch3.Sets-and-logic

module Ch4.1-Quasi-inverses ⦃ fe : FunExt ⦄ ⦃ univ : Univalence ⦄ where


-- Lemma 4.1.1 (If f is quasi-invertible, then qinv f ≃ (id ∼ id)

inhabited-qinv-is-𝑖𝑑∼𝑖𝑑' : {A B : 𝓤 ̇} (p : A ≡ B) → qinv (pr₁ (idtoeqv p)) ≃ (𝑖𝑑 A ∼ 𝑖𝑑 A)
inhabited-qinv-is-𝑖𝑑∼𝑖𝑑' {𝓤} {A} {.A} (refl .A) =
  qinv (𝑖𝑑 A)
    ≃⟨ Σ-preserves-family-≃ (λ g → ×-preserves-≃ (≃-sym (happly , happly-is-equiv)) (≃-sym (happly , happly-is-equiv))) ⟩
  (Σ g ꞉ (A → A) , (g ≡ 𝑖𝑑 A) × (g ≡ 𝑖𝑑 A))
    ≃⟨ Σ-assoc _ _ _ ⟩
  (Σ h ꞉ (Σ g ꞉ (A → A) , g ≡ 𝑖𝑑 A) , pr₁ h ≡ 𝑖𝑑 A)
    ≃⟨ Σ-over-Contr-base-is-fib _ _ (free-left-endpt-is-Contr _ _) ⟩
  (𝑖𝑑 A ≡ 𝑖𝑑 A)
    ≃⟨ happly , happly-is-equiv ⟩
  (𝑖𝑑 A ∼ 𝑖𝑑 A) ■

inhabited-qinv-is-𝑖𝑑∼𝑖𝑑 : {A B : 𝓤 ̇} (f : A → B) → qinv f → qinv f ≃ (𝑖𝑑 A ∼ 𝑖𝑑 A)
inhabited-qinv-is-𝑖𝑑∼𝑖𝑑 {𝓤} {A} {B} f q =
  let e : isequiv f
      e = qinv-to-isequiv q
      p = A ≡ B
      p = ua (f , e)
  in qinv f
       ≃⟨ idtoeqv (ap (qinv ∘ pr₁) (idtoeqv-β' (f , e) ⁻¹)) ⟩
     qinv (pr₁ (idtoeqv (ua (f , qinv-to-isequiv q))))
       ≃⟨ inhabited-qinv-is-𝑖𝑑∼𝑖𝑑' p ⟩
     (𝑖𝑑 A ∼ 𝑖𝑑 A) ■


-- Lemma 4.1.2

-- Theorem 4.1.3

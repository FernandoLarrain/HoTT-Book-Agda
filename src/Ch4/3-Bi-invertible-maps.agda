{-# OPTIONS --without-K --exact-split --safe #-}

open import Ch1.Type-theory
open import Ch2.Homotopy-type-theory
open import Ch3.Sets-and-logic
open import Ch4.2-Half-adjoint-equivalences

module Ch4.3-Bi-invertible-maps where


-- Definition 4.3.1 (Bi-invertible maps).

{-  In the book, biinv is definitionally equal to isequiv only up to a reordering of factors. Here, we use the same order for both. -}

biinv : {A : 𝓤 ̇} {B : 𝓥 ̇} (f : A → B) → 𝓤 ⊔ 𝓥 ̇
biinv {𝓤} {𝓥} {A} {B} f = sec f × ret f

module biinv {A : 𝓤 ̇} {B : 𝓥 ̇} {f : A → B} where

  biinv₁ : biinv f → B → A
  biinv₁ ((g , α) , (h , β)) = g

  biinv₂ : (e : biinv f) → (f ∘ biinv₁ e ∼ id)
  biinv₂ ((g , α) , (h , β)) = α

  biinv₃ : biinv f → B → A
  biinv₃ ((g , α) , (h , β)) = h

  biinv₄ : (e : biinv f) → (biinv₃ e ∘ f ∼ id)
  biinv₄ ((g , α) , (h , β)) = β

open biinv public


qinv-to-biinv : {A : 𝓤 ̇} {B : 𝓥 ̇} {f : A → B} → qinv f → biinv f
qinv-to-biinv (g , α , β) = (g , α) , (g , β)

biinv-to-qinv : {A : 𝓤 ̇} {B : 𝓥 ̇} {f : A → B} → biinv f → qinv f
biinv-to-qinv {𝓤} {𝓥} {A} {B} {f} ((g , α) , (h , β)) =
  g ,
  α ,
  λ x → hsym β (g (f x)) ∙ (ap h (α (f x)) ∙ β x)  


-- Theorem 4.3.2 (biinv f is a proposition).

biinv-is-Prop : ⦃ fe : FunExt ⦄ {A : 𝓤 ̇} {B : 𝓥 ̇} (f : A → B) → isProp (biinv f)
biinv-is-Prop f = suffices λ ib → ×-preserves-Contr (sec f) (ret f) (sec-of-qinv-is-Contr f (biinv-to-qinv ib)) (ret-of-qinv-is-Contr f (biinv-to-qinv ib))
  where
  suffices : (biinv f → isContr (biinv f)) → isProp (biinv f)
  suffices = inv (isProp-≃-inhabited-to-isContr (biinv f))


-- Corollary 4.3.3 (biinv is equivalent to ishae).

biinv-to-ishae : {A : 𝓤 ̇} {B : 𝓥 ̇} (f : A → B) → biinv f → ishae f
biinv-to-ishae f = qinv-to-ishae ∘ biinv-to-qinv

ishae-to-biinv : {A : 𝓤 ̇} {B : 𝓥 ̇} (f : A → B) → ishae f → biinv f
ishae-to-biinv f = qinv-to-biinv ∘ ishae-to-qinv

biinv-≃-ishae : ⦃ fe : FunExt ⦄ {A : 𝓤 ̇} {B : 𝓥 ̇} (f : A → B) → biinv f ≃ ishae f
biinv-≃-ishae f = ⇔-to-≃ (biinv-is-Prop f) (ishae-is-Prop f) (biinv-to-ishae f , ishae-to-biinv f)
  
 
  







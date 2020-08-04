{-# OPTIONS --without-K --exact-split --rewriting #-}

open import Ch1.3-Universes-and-families

module Rewrite where

-- The rewrite relation _↦_.

{- Agda has no native support for HITs, so we have to postulate them. To obtain definitonal equality for point constructors, we extend Agda's evaluation relation with new computation rules defined via _↦_ -}

postulate

  _↦_ : {𝓤 : Universe} {A : 𝓤 ̇} → A → A → 𝓤 ̇

infix 0 _↦_

{-# BUILTIN REWRITE _↦_ #-} 

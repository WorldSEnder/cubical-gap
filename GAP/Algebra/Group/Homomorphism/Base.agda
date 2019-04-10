{-# OPTIONS --cubical #-}

module GAP.Algebra.Group.Homomorphism.Base where

open import Cubical.Core.Prelude
open import GAP.Algebra.Group.Base

record _⟶_ {ℓ ℓ'} (src : Group ℓ) (trgt : Group ℓ') : Set (ℓ-max ℓ ℓ') where
  open Group
  private
    _∘_ = src ._·_
    _⋆_ = trgt ._·_
  field
    map : src .Carrier → trgt .Carrier
    map-distrib : ∀ a b → map (a ∘ b) ≡ map a ⋆ map b

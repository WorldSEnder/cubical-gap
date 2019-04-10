{-# OPTIONS --cubical #-}

module GAP.Algebra.Group.Isomorphism.Base where

open import Cubical.Core.Prelude
open import GAP.Algebra.Group.Base
open import GAP.Algebra.Group.Homomorphism

record _↔_ {ℓ ℓ'} (src : Group ℓ) (trgt : Group ℓ') : Set (ℓ-max ℓ ℓ') where
  field
    fun : src ⟶ trgt
    inv : trgt ⟶ src
    fg≡id : fun ∘hom inv ≡ idHom trgt
    gf≡id : inv ∘hom fun ≡ idHom src

{-# OPTIONS --cubical #-}

module GAP.Algebra.Group.Base where

open import Cubical.Core.Prelude
open import GAP.FunctionProperties

record RawGroup ℓ : Set (ℓ-suc ℓ) where
  field
    Carrier : Set ℓ
    _·_ : Op₂ Carrier

record IsWeakLeftGroup {ℓ} (raw : RawGroup ℓ) : Set ℓ where
  open RawGroup raw public
  field
    isSetCarrier : isSet Carrier
    e : Op₀ Carrier
    _⁻¹ : Op₁ Carrier
    assoc : Associative _·_
    id-l : ∀ a → e · a ≡ a
    inv-l : ∀ a → (a ⁻¹) · a ≡ e

record IsGroup {ℓ} (raw : RawGroup ℓ) : Set ℓ where
  open RawGroup raw public
  field
    isSetCarrier : isSet Carrier
    e : Op₀ Carrier
    _⁻¹ : Op₁ Carrier
    assoc : Associative _·_
    id-l : ∀ a → e · a ≡ a
    id-r : ∀ a → a · e ≡ a
    inv-l : ∀ a → (a ⁻¹) · a ≡ e
    inv-r : ∀ a → a · (a ⁻¹) ≡ e

record Group ℓ : Set (ℓ-suc ℓ) where
  field
    rawGroup : RawGroup ℓ
    isGroup : IsGroup rawGroup
  open IsGroup isGroup public

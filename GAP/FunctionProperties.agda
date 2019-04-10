{-# OPTIONS --cubical #-}

module GAP.FunctionProperties where

open import Cubical.Core.Prelude

private
  variable
    ℓ : Level
    A : Set ℓ

Op₀ : (A : Set ℓ) → Set ℓ
Op₀ A = A

Op₁ : (A : Set ℓ) → Set ℓ
Op₁ A = A → A

Op₂ : (A : Set ℓ) → Set ℓ
Op₂ A = A → A → A

Associative : Op₂ A → Set _
Associative _·_ = ∀ a b c → a · (b · c) ≡ (a · b) · c

Involutive : Op₁ A → Set _
Involutive _ᵀ = ∀ a → a ᵀ ᵀ ≡ a

Injective : Op₁ A → Set _
Injective f = ∀ a b → f a ≡ f b → a ≡ b

involutive→injective : {op : Op₁ A} → Involutive op → Injective op
involutive→injective {op = f} involutive a b fa≡fb =
  a       ≡⟨ sym (involutive a) ⟩
  f (f a) ≡[ i ]⟨ f (fa≡fb i) ⟩
  f (f b) ≡⟨ involutive b ⟩
  b       ∎

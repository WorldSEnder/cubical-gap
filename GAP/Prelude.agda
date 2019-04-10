{-# OPTIONS --cubical #-}

module GAP.Prelude where

open import Cubical.Core.Prelude public

infix 3 _≡[_]≡_
_≡[_]≡_ : ∀ {ℓ ℓ'} {A : Set ℓ} {B : A → Set ℓ'}
        → ∀ {x y} → B x → (p : x ≡ y) → B y → Set _
_≡[_]≡_ {B = B} x p y = PathP (λ i → B (p i)) x y

setComp : ∀ {ℓ} {A : Set ℓ} {w x y z : A}
        → (p : w ≡ x) (q : y ≡ z)
        → (r : w ≡ y) (s : x ≡ z)
        → isSet A
        → PathP (λ i → r i ≡ s i) p q
setComp {ℓ = ℓ} {A = A} p q r s isSetA = isProp→PathP uncurryIsSetA (λ i → r i , s i) p q where
  -- this is the same as A ×Σ A but due to dependency, we write a quick inline definition
  record UncurryHelper : Set ℓ where
    constructor _,_
    field
      proj₁ : A
      proj₂ : A
  open UncurryHelper
  uncurryIsSetA : (as : UncurryHelper) → isProp (proj₁ as ≡ proj₂ as)
  uncurryIsSetA (a , b) = isSetA a b

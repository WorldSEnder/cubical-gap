{-# OPTIONS --cubical #-}

module GAP.Algebra.Group.Properties where

open import GAP.Algebra.Group.Base

open import Cubical.Core.Prelude
open import GAP.FunctionProperties

private
  variable
    ℓ : Level
    raw : RawGroup ℓ

weakLeft→full : IsWeakLeftGroup raw → IsGroup raw
weakLeft→full weakleft = record
  { isSetCarrier = isSetCarrier
  ; e = e
  ; _⁻¹ = _⁻¹
  ; assoc = assoc
  ; id-l = id-l
  ; id-r = id-r
  ; inv-l = inv-l
  ; inv-r = inv-r
  } where
  open IsWeakLeftGroup weakleft
  inv-r : ∀ a → a · (a ⁻¹) ≡ e
  inv-r a =
    a · b             ≡[ i ]⟨ id-l (a · b) (~ i) ⟩
    e · (a · b)       ≡[ i ]⟨ inv-l b (~ i) · (a · b) ⟩
    (c · b) · (a · b) ≡⟨ sym (assoc _ _ _) ⟩
    c · (b · (a · b)) ≡[ i ]⟨ c · assoc b a b i ⟩
    c · ((b · a) · b) ≡[ i ]⟨ c · (inv-l a i · b) ⟩
    c · (e · b)       ≡[ i ]⟨ c · id-l b i ⟩
    c · b             ≡[ i ]⟨ inv-l b i ⟩
    e                 ∎
    where
      b = a ⁻¹
      c = b ⁻¹
  id-r : ∀ a → a · e ≡ a
  id-r a =
    a · e       ≡[ i ]⟨ a · inv-l a (~ i) ⟩
    a · (b · a) ≡⟨ assoc _ _ _ ⟩
    (a · b) · a ≡[ i ]⟨ inv-r a i · a ⟩
    e · a       ≡⟨ id-l a ⟩
    a           ∎
    where
      b = a ⁻¹

module Internal (group : Group ℓ) where
  open Group group
  private
    variable
      a b c : Carrier

  e-unique : (∀ f → a · f ≡ f) → a ≡ e
  e-unique {a = a} idf =
    a     ≡⟨ sym (id-r a) ⟩
    a · e ≡⟨ idf e ⟩
    e     ∎

  inv-unique : b · a ≡ e → a ⁻¹ ≡ b
  inv-unique {b = b} {a = a} ba≡e =
    (a ⁻¹)           ≡⟨ sym (id-l _) ⟩
    e · (a ⁻¹)       ≡[ i ]⟨ ba≡e (~ i) · (a ⁻¹) ⟩
    (b · a) · (a ⁻¹) ≡⟨ sym (assoc _ _ _) ⟩
    b · (a · (a ⁻¹)) ≡[ i ]⟨ b · inv-r a i ⟩
    b · e            ≡⟨ id-r b ⟩
    b                ∎

  inv-involutive : Involutive _⁻¹
  inv-involutive a = inv-unique (inv-r a)

  inv-injective : Injective _⁻¹
  inv-injective = involutive→injective inv-involutive

  e-inv≡e : e ⁻¹ ≡ e
  e-inv≡e = inv-unique (id-r e)

  [ab]'≡b'a' : (a · b) ⁻¹ ≡ (b ⁻¹) · (a ⁻¹)
  [ab]'≡b'a' {a = a} {b = b} = inv-unique b'a'ab≡e where
    b'a'ab≡e : ((b ⁻¹) · (a ⁻¹)) · (a · b) ≡ e
    b'a'ab≡e =
      ((b ⁻¹) · (a ⁻¹)) · (a · b) ≡⟨ sym (assoc _ _ _) ⟩
      (b ⁻¹) · ((a ⁻¹) · (a · b)) ≡[ i ]⟨ (b ⁻¹) · assoc (a ⁻¹) a b i ⟩
      (b ⁻¹) · (((a ⁻¹) · a) · b) ≡[ i ]⟨ (b ⁻¹) · (inv-l a i · b) ⟩
      (b ⁻¹) · (e · b)            ≡[ i ]⟨ (b ⁻¹) · id-l b i ⟩
      (b ⁻¹) · b                  ≡⟨ inv-l b ⟩
      e                           ∎

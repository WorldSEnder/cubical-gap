{-# OPTIONS --cubical #-}

module GAP.Algebra.Group.Constructions where

open import Cubical.Core.Prelude
open import Cubical.Data.Unit
open import GAP.Algebra.Group.Base
open import GAP.Algebra.Group.Properties
open import GAP.Algebra.Group.Homomorphism
  renaming (module Homology to HHomology)
open import GAP.Algebra.Group.Isomorphism
  renaming (module Homology to IHomology)
open import GAP.FunctionProperties

private
  variable
    ℓ ℓ' ℓ'' : Level

_ᵒᵖ : Group ℓ → Group ℓ
grp ᵒᵖ = record
  { rawGroup = record
    { Carrier = Carrier
    ; _·_ = λ a b → b · a
    }
  ; isGroup = record
    { isSetCarrier = isSetCarrier
    ; e = e
    ; _⁻¹ = _⁻¹
    ; assoc = λ a b c → sym (assoc c b a)
    ; id-l = id-r
    ; id-r = id-l
    ; inv-l = inv-r
    ; inv-r = inv-l
    }
  } where open Group grp

ᵒᵖ-involutive : Involutive (_ᵒᵖ {ℓ = ℓ})
ᵒᵖ-involutive grp = refl

trivialGroup : Group ℓ-zero
trivialGroup = record
  { rawGroup = rawTrivialGroup
  ; isGroup = weakLeft→full isWeakLeftGroup
  } where
  rawTrivialGroup : RawGroup ℓ-zero
  rawTrivialGroup = record
    { Carrier = Unit
    ; _·_ = λ { tt tt → tt }
    }
  isWeakLeftGroup : IsWeakLeftGroup rawTrivialGroup
  isWeakLeftGroup = record
    { isSetCarrier = isProp→isSet isPropUnit
    ; e = tt
    ; _⁻¹ = λ { tt → tt }
    ; assoc = λ a b c → refl
    ; id-l = λ a → refl
    ; inv-l = λ a →  refl
    }

terminalHom : (grp : Group ℓ) → grp ⟶ trivialGroup
terminalHom grp = record
  { map = λ a → tt
  ; map-distrib = λ a b →  refl
  }

terminalHomUnique : {grp : Group ℓ} → (hom : grp ⟶ trivialGroup) → hom ≡ terminalHom grp
terminalHomUnique {grp = grp} hom = HHomology.hom-eq hom (terminalHom grp) (funExt (λ a → refl))

Int-Group : Group ℓ-zero
Int-Group = record
  { rawGroup = rawIntGroup
  ; isGroup = weakLeft→full intIsWeakLeftGroup
  } where
  open import Cubical.Data.Int
  rawIntGroup : RawGroup ℓ-zero
  rawIntGroup = record
    { Carrier = Int
    ; _·_ = _+_
    }
  intIsWeakLeftGroup : IsWeakLeftGroup rawIntGroup
  intIsWeakLeftGroup = record
    { isSetCarrier = isSetInt
    ; e = pos 0
    ; _⁻¹ = λ a → pos 0 - a
    ; assoc = +-assoc
    ; id-l = λ a → sym (pos0+ a)
    ; inv-l = λ a → minusPlus a (pos 0) 
    }

_⊙_ : Group ℓ → Group ℓ' → Group (ℓ-max ℓ ℓ')
g₁ ⊙ g₂ = record
  { rawGroup = rawProdGroup
  ; isGroup = weakLeft→full prodIsWeakLeftGroup
  } where
  open import Cubical.Data.Prod
  open Group
  G₁ = g₁ .Carrier
  _*_ = g₁ ._·_
  G₂ = g₂ .Carrier
  _⋆_ = g₂ ._·_
  rawProdGroup : RawGroup _
  rawProdGroup = record
    { Carrier = g₁ .Carrier × g₂ .Carrier
    ; _·_ = λ { (a₁ , b₁) (a₂ , b₂) → (a₁ * a₂) , (b₁ ⋆ b₂) }
    }
  prodIsWeakLeftGroup : IsWeakLeftGroup rawProdGroup
  prodIsWeakLeftGroup = record
    { isSetCarrier = hLevelProd 2 (g₁ .isSetCarrier) (g₂ .isSetCarrier)
    ; e = g₁ .e , g₂ .e
    ; _⁻¹ = λ { (a , b) → (g₁ ⁻¹) a , (g₂ ⁻¹) b }
    ; assoc = λ { (a₁ , a₂) (b₁ , b₂) (c₁ , c₂) i → g₁ .assoc a₁ b₁ c₁ i , g₂ .assoc a₂ b₂ c₂ i }
    ; id-l = λ { (a₁ , a₂) i → g₁ .id-l a₁ i , g₂ .id-l a₂ i }
    ; inv-l = λ { (a₁ , a₂) i → g₁ .inv-l a₁ i , g₂ .inv-l a₂ i }
    }

Aut : Group ℓ → Group ℓ
Aut G = record
  { rawGroup = rawAutGroup
  ; isGroup = isGroupAut
  } where
  open Group
  _op_ = (_∘iso_ {ga = G} {G} {G})
  rawAutGroup : RawGroup _
  rawAutGroup = record
    { Carrier = G ↔ G
    ; _·_ = _op_
    }
  isGroupAut : IsGroup rawAutGroup
  isGroupAut = record
    { isSetCarrier = isSetIso G G
    ; e = idIso G
    ; _⁻¹ = invIso
    ; assoc = associativity
    ; id-l = identity-l
    ; id-r = ∘iso-id-l
    ; inv-l = ∘iso-inv-l
    ; inv-r = ∘iso-inv-r
    } where
    id : G ↔ G
    id = idIso G
    associativity : Associative _op_
    associativity = ∘iso-assoc
    identity-l : ∀ a → id op a ≡ a
    identity-l = ∘iso-id-r

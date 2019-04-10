{-# OPTIONS --cubical #-}

module GAP.Algebra.Group.Homomorphism.Properties where

open import GAP.Prelude
open import Cubical.Core.Glue
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.PathSplitEquiv
open import Cubical.Foundations.Transport
open import Cubical.Data.Sigma
open import GAP.Algebra.Group.Base
open import GAP.Algebra.Group.Homomorphism.Base
open Group
open _⟶_

idHom : ∀ {ℓ} (grp : Group ℓ) → grp ⟶ grp
idHom grp = record
  { map = idfun (grp .Carrier)
  ; map-distrib = λ a b → refl
  }

_∘hom_ : ∀ {ℓ ℓ' ℓ''} {ga : Group ℓ} {gb : Group ℓ'} {gc : Group ℓ''}
       → (gb ⟶ gc) → (ga ⟶ gb) → (ga ⟶ gc)
b⟶c ∘hom a⟶b = record
  { map = b⟶c .map ∘ a⟶b .map
  ; map-distrib = λ a b → cong (b⟶c .map) (a⟶b .map-distrib a b) ∙ b⟶c .map-distrib _ _
  }

private
  module AsSigma {ℓ ℓ'} (src : Group ℓ) (trgt : Group ℓ') where
    _*_ = src ._·_
    _⋆_ = trgt ._·_

    ΣA = src .Carrier → trgt .Carrier
    ΣB : ΣA → Set _
    ΣB m = ∀ a b → m (a * b) ≡ m a ⋆ m b

    isSetΣA : isSet ΣA
    isSetΣA = isSetPi (λ _ → isSetCarrier trgt)

    isPropΣB : ∀ σa → isProp (ΣB σa)
    isPropΣB σa = hLevelPi 1 λ a → hLevelPi 1 λ b → isSetCarrier trgt _ _

    homAsSigma : src ⟶ trgt ≃ Σ ΣA ΣB
    homAsSigma = isoToEquiv (iso (λ morph → (morph .map , morph .map-distrib))
                            (λ { (m , md) → record { map = m ; map-distrib = md } })
                            (λ m → refl)
                            (λ s → refl))

module Homology {ℓ ℓ'} {src : Group ℓ} {trgt : Group ℓ'}
                (g h : src ⟶ trgt) where
  open AsSigma src trgt

  abstract
    isInhabDistrib : (gmap≡hmap : g .map ≡ h .map)
                   → g .map-distrib ≡[ gmap≡hmap ]≡ h .map-distrib
    isInhabDistrib gmap≡hmap = gh-map-distrib where
      g≡h : ∀ s → g .map s ≡ h .map s
      g≡h s i = gmap≡hmap i s
      gh-map-distrib : PathP _ _ _
      gh-map-distrib i a b = setComp (g .map-distrib a b) (h .map-distrib a b)
                                     (g≡h (a * b)) (λ j → g≡h a j ⋆ g≡h b j)
                                     (trgt .isSetCarrier) i

  hom≡ : (g ≡ h) ≃ (g .map ≡ h .map)
  hom≡ = compEquiv step1 (compEquiv step2 step3) where
    step1 : (g ≡ h) ≃ ((g .map , g .map-distrib) ≡ (h .map , h .map-distrib))
    step1 = congEquiv homAsSigma

    step2 : ((g .map , g .map-distrib) ≡ (h .map , h .map-distrib)) ≃
            (Σ (g .map ≡ h .map) (g .map-distrib ≡[_]≡ h .map-distrib))
    step2 = invEquiv Σ≡

    step3 : (Σ (g .map ≡ h .map) (g .map-distrib ≡[_]≡ h .map-distrib)) ≃
            (g .map ≡ h .map)
    step3 = isoToEquiv (iso fst (λ gm≡hm → (gm≡hm , isInhabDistrib gm≡hm)) (λ _ → refl) elim-intro) where
      elim-intro : ∀ a → _
      elim-intro (m , d) = ΣPathP (refl , isProp→isPropPathP isPropΣB m (g .map-distrib) (h .map-distrib) (isInhabDistrib m) d)

  isPropMapG≡MapH : isProp (g .map ≡ h .map)
  isPropMapG≡MapH = isSetΣA (g .map) (h .map)

  isPropG≡H : isProp (g ≡ h)
  isPropG≡H = subst isProp (ua (invEquiv hom≡)) isPropMapG≡MapH

  hom-eq : (g .map ≡ h .map) → (g ≡ h)
  hom-eq = equivFun (invEquiv hom≡)

isSetHom : ∀ {ℓ ℓ'} (src : Group ℓ) (trgt : Group ℓ')
         → isSet (src ⟶ trgt)
isSetHom src trgt = Homology.isPropG≡H

∘hom-id-l : ∀ {ℓ ℓ'} {ga : Group ℓ} {gb : Group ℓ'}
          → (a : ga ⟶ gb)
          → a ∘hom idHom ga ≡ a
∘hom-id-l a = Homology.hom-eq _ _ (∘-idˡ _) -- refl would work, but let's keep it more readable

∘hom-id-r : ∀ {ℓ ℓ'} {ga : Group ℓ} {gb : Group ℓ'}
          → (a : ga ⟶ gb)
          → idHom gb ∘hom a ≡ a
∘hom-id-r a = Homology.hom-eq _ _ (∘-idʳ _) -- refl would work, but let's keep it more readable

∘hom-assoc : ∀ {ℓ ℓ' ℓ'' ℓ'''} {ga : Group ℓ} {gb : Group ℓ'} {gc : Group ℓ''} {gd : Group ℓ'''}
           → (a : gc ⟶ gd) (b : gb ⟶ gc) (c : ga ⟶ gb)
           →  a ∘hom (b ∘hom c) ≡ (a ∘hom b) ∘hom c
∘hom-assoc a b c = Homology.hom-eq _ _ (∘-assoc (a .map) (b .map) (c .map)) where open _⟶_

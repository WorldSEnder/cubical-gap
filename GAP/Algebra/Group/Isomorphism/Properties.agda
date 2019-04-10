{-# OPTIONS --cubical #-}

module GAP.Algebra.Group.Isomorphism.Properties where

open import GAP.Prelude
open import Cubical.Data.Prod
open import Cubical.Data.Sigma
open import Cubical.Core.Glue
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.PathSplitEquiv
open import GAP.Algebra.Group.Base
open import GAP.Algebra.Group.Homomorphism
  renaming (module Homology to HHomology)
open import GAP.Algebra.Group.Isomorphism.Base
open Group
open _⟶_
open _↔_

_∘iso_ : ∀ {ℓ ℓ' ℓ''} {ga : Group ℓ} {gb : Group ℓ'} {gc : Group ℓ''}
       → (gb ↔ gc) → (ga ↔ gb) → (ga ↔ gc)
b↔c ∘iso a↔b = record
  { fun = b↔c .fun ∘hom a↔b .fun
  ; inv = a↔b .inv ∘hom b↔c .inv
  ; fg≡id = f∘isog≡id
  ; gf≡id = g∘isof≡id
  } where
  open _↔_
  a⟶b = a↔b .fun
  b⟶c = b↔c .fun
  b⟶a = a↔b .inv
  c⟶b = b↔c .inv
  f∘isog≡id =
    ((b⟶c ∘hom a⟶b) ∘hom (b⟶a ∘hom c⟶b)) ≡⟨ sym (∘hom-assoc b⟶c a⟶b _) ⟩
    (b⟶c ∘hom (a⟶b ∘hom (b⟶a ∘hom c⟶b))) ≡[ i ]⟨ b⟶c ∘hom (∘hom-assoc a⟶b b⟶a c⟶b i) ⟩
    (b⟶c ∘hom ((a⟶b ∘hom b⟶a) ∘hom c⟶b)) ≡[ i ]⟨ b⟶c ∘hom ((a↔b .fg≡id i) ∘hom c⟶b) ⟩
    (b⟶c ∘hom (idHom _ ∘hom c⟶b))        ≡⟨ cong (b⟶c ∘hom_) (∘hom-id-r _) ⟩
    (b⟶c ∘hom c⟶b)                       ≡⟨ b↔c .fg≡id ⟩
    idHom _                              ∎
  g∘isof≡id : _
  g∘isof≡id =
    ((b⟶a ∘hom c⟶b) ∘hom (b⟶c ∘hom a⟶b)) ≡⟨ sym (∘hom-assoc b⟶a c⟶b _) ⟩
    (b⟶a ∘hom (c⟶b ∘hom (b⟶c ∘hom a⟶b))) ≡[ i ]⟨ b⟶a ∘hom (∘hom-assoc c⟶b b⟶c a⟶b i) ⟩
    (b⟶a ∘hom ((c⟶b ∘hom b⟶c) ∘hom a⟶b)) ≡[ i ]⟨ b⟶a ∘hom ((b↔c .gf≡id i) ∘hom a⟶b) ⟩
    (b⟶a ∘hom (idHom _ ∘hom a⟶b))        ≡⟨ cong (b⟶a ∘hom_) (∘hom-id-r _) ⟩
    (b⟶a ∘hom a⟶b)                       ≡⟨ a↔b .gf≡id ⟩
    idHom _                              ∎

private
  module AsSigma {ℓ ℓ'} (ga : Group ℓ) (gb : Group ℓ') where
    ΣA : Set _
    ΣA = (ga ⟶ gb) ×Σ (gb ⟶ ga)
    ΣB : ΣA → Set _
    ΣB (f , g) = (f ∘hom g ≡ idHom gb) ×Σ (g ∘hom f ≡ idHom ga)

    isSetΣA : isSet ΣA
    isSetΣA = isOfHLevelΣ 2 (isSetHom ga gb) (λ _ → isSetHom gb ga)

    isPropΣB : ∀ σa → isProp (ΣB σa)
    isPropΣB (f , g) = isOfHLevelΣ 1 (HHomology.isPropG≡H _ _) (λ _ → HHomology.isPropG≡H _ _)

    σa : ga ↔ gb → ΣA
    σa ↔ = ↔ .fun , ↔ .inv

    σb : (↔ : ga ↔ gb) → ΣB (σa ↔)
    σb ↔ = ↔ .fg≡id , ↔ .gf≡id

    isoAsSigma : ga ↔ gb ≃ Σ ΣA ΣB
    isoAsSigma = isoToEquiv (iso (λ ↔ → σa ↔ , σb ↔)
                                 (λ { (σa , σb) → record { fun = σa .fst; inv = σa .snd
                                                         ; fg≡id = σb .fst ; gf≡id = σb .snd } })
                                 (λ s → refl)
                                 (λ m → refl))

module Homology {ℓ ℓ'} {ga : Group ℓ} {gb : Group ℓ'}
                (g h : ga ↔ gb) where
  open AsSigma ga gb

--  private
  abstract
    -- having this abstract prevents some sort of slow progress
    -- in the type checker! investigate possible causes!!
    isInhabDistrib : (σa≡ : σa g ≡ σa h)
                   → PathP (λ i → ΣB (σa≡ i)) (σb g) (σb h)
    isInhabDistrib σa≡ = isProp→PathP isPropΣB σa≡ (σb g) (σb h)

  hom≡ : (g ≡ h) ≃ (g .fun ≡ h .fun) ×Σ (g .inv ≡ h .inv)
  hom≡ = compEquiv step1 (compEquiv step2 (compEquiv step3 step4)) where
    step1 : (g ≡ h) ≃ ((σa g , σb g) ≡ (σa h , σb h))
    step1 = congEquiv isoAsSigma

    step2 : ((σa g , σb g) ≡ (σa h , σb h)) ≃
            (Σ (σa g ≡ σa h) (σb g ≡[_]≡ σb h))
    step2 = invEquiv Σ≡

    step3 : (Σ (σa g ≡ σa h) (σb g ≡[_]≡ σb h)) ≃
            (σa g ≡ σa h)
    step3 = isoToEquiv (iso fst (λ gm≡hm → (gm≡hm , isInhabDistrib gm≡hm)) (λ _ → refl) elim-intro) where
      elim-intro : ∀ a → _
      elim-intro (m , d) = ΣPathP (refl , isProp→isPropPathP isPropΣB m (σb g) (σb h) (isInhabDistrib m) d)

    step4 : (σa g ≡ σa h) ≃ (g .fun ≡ h .fun) ×Σ (g .inv ≡ h .inv)
    step4 = invEquiv Σ≡

  hom-eq : (g .fun ≡ h .fun) ×Σ (g .inv ≡ h .inv) → g ≡ h
  hom-eq = equivFun (invEquiv hom≡)

  isPropG≡H : isProp (g ≡ h)
  isPropG≡H = subst isProp (ua (invEquiv hom≡)) (isOfHLevelΣ 1 (HHomology.isPropG≡H _ _) (λ _ → HHomology.isPropG≡H _ _))

isSetIso : ∀ {ℓ ℓ'} (src : Group ℓ) (trgt : Group ℓ')
         → isSet (src ↔ trgt)
isSetIso src trgt = Homology.isPropG≡H

idIso : ∀ {ℓ} (ga : Group ℓ) → ga ↔ ga
idIso ga = record
  { fun = idHom ga
  ; inv = idHom ga
  ; fg≡id = ∘hom-id-l _
  ; gf≡id = ∘hom-id-r _
  }

invIso : ∀ {ℓ ℓ'} {ga : Group ℓ} {gb : Group ℓ'}
       → ga ↔ gb
       → gb ↔ ga
invIso ga↔gb = record
  { fun = ga↔gb .inv
  ; inv = ga↔gb .fun
  ; fg≡id = ga↔gb .gf≡id
  ; gf≡id = ga↔gb .fg≡id
  }

∘iso-inv-l : ∀ {ℓ ℓ'} {ga : Group ℓ} {gb : Group ℓ'}
           → (ga↔gb : ga ↔ gb)
           → (invIso ga↔gb) ∘iso ga↔gb ≡ idIso ga
∘iso-inv-l ga↔gb = Homology.hom-eq _ _ (ga↔gb .gf≡id , ga↔gb .gf≡id)

∘iso-inv-r : ∀ {ℓ ℓ'} {ga : Group ℓ} {gb : Group ℓ'}
           → (ga↔gb : ga ↔ gb)
           → ga↔gb ∘iso (invIso ga↔gb) ≡ idIso gb
∘iso-inv-r ga↔gb = Homology.hom-eq _ _ (ga↔gb .fg≡id , ga↔gb .fg≡id)

∘iso-id-l : ∀ {ℓ ℓ'} {ga : Group ℓ} {gb : Group ℓ'}
          → (ga↔gb : ga ↔ gb)
          → ga↔gb ∘iso idIso ga ≡ ga↔gb
∘iso-id-l ga↔gb = Homology.hom-eq _ _ (∘hom-id-l _ , ∘hom-id-r _)

∘iso-id-r : ∀ {ℓ ℓ'} {ga : Group ℓ} {gb : Group ℓ'}
          → (ga↔gb : ga ↔ gb)
          → idIso gb ∘iso ga↔gb ≡ ga↔gb
∘iso-id-r ga↔gb = Homology.hom-eq _ _ (∘hom-id-r _ , ∘hom-id-l _)


∘iso-assoc : ∀ {ℓ ℓ' ℓ'' ℓ'''} {ga : Group ℓ} {gb : Group ℓ'} {gc : Group ℓ''} {gd : Group ℓ'''}
           → (a : gc ↔ gd) (b : gb ↔ gc) (c : ga ↔ gb)
           →  a ∘iso (b ∘iso c) ≡ (a ∘iso b) ∘iso c
∘iso-assoc a b c = Homology.hom-eq _ _ (∘hom-assoc (a .fun) (b .fun) (c .fun) , sym (∘hom-assoc (c .inv) (b .inv) (a .inv)))

-- importantly ↔ is stronger than Iso (exactly by map-distrib)
↔ToCarrierIso : ∀ {ℓ ℓ'} {ga : Group ℓ} {gb : Group ℓ'}
              → ga ↔ gb
              → Iso (ga .Carrier) (gb .Carrier)
↔ToCarrierIso ga↔gb = record
  { fun = ga↔gb .fun .map
  ; inv = ga↔gb .inv .map
  ; rightInv = λ b i → ga↔gb .fg≡id i .map b
  ; leftInv  = λ b i → ga↔gb .gf≡id i .map b
  }

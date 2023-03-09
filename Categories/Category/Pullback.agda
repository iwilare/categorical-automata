{-# OPTIONS --without-K --safe #-}
module Categories.Category.Pullback where

open import Level
open import Function using () renaming (_∘_ to _∙_)
open import Data.Product using (_×_; Σ; Σ-syntax; _,_; proj₁; proj₂; zip; map; <_,_>; swap)

open import Categories.Utils.Product
open import Categories.Category using (Category)
open import Categories.Category.Groupoid using (IsGroupoid)
open import Categories.Functor renaming (id to idF)
open import Categories.NaturalTransformation.Core
open import Categories.NaturalTransformation.NaturalIsomorphism hiding (refl)
import Categories.Morphism as Morphism

private
  variable
    o ℓ e o′ ℓ′ e′ o″ ℓ″ e″ : Level
    o₁ ℓ₁ e₁ o′₁ ℓ′₁ e′₁ o₂ ℓ₂ e₂ o′₂ ℓ′₂ e′₂ : Level

    C C₁ C₂ D D₁ D₂ : Category o ℓ e

Product : (C : Category o ℓ e) (D : Category o′ ℓ′ e′) (E : Category o″ ℓ″ e″) (F : Functor C E) (G : Functor D E)
        → Category (o ⊔ o′ ⊔ o″) (ℓ ⊔ ℓ′ ⊔ ℓ″) (e ⊔ e′ ⊔ e″)
Product C D E F G = record
  { Obj       = Σ[ c ∈ C.Obj ] Σ[ d ∈ C.Obj ] {! (F.₀ c E.≈ G.₀ d)  !} --C.Obj × D.Obj
  ; _⇒_       = {!   !} --C._⇒_ -< _×_ >- D._⇒_
  ; _≈_       = {!   !} --C._≈_ -< _×_ >- D._≈_
  ; _∘_       = {!   !} --zip C._∘_ D._∘_
  ; id        = {!   !} --C.id , D.id
  ; assoc     = {!   !} --C.assoc , D.assoc
  ; sym-assoc = {!   !} --C.sym-assoc , D.sym-assoc
  ; identityˡ = {!   !} --C.identityˡ , D.identityˡ
  ; identityʳ = {!   !} --C.identityʳ , D.identityʳ
  ; identity² = {!   !} --C.identity² , D.identity²
  ; equiv     = {!   !}
  --record
  --  { refl  = C.Equiv.refl , D.Equiv.refl
  --  ; sym   = map C.Equiv.sym D.Equiv.sym
  --  ; trans = zip C.Equiv.trans D.Equiv.trans
  --  }
  ; ∘-resp-≈  = {!   !} --zip C.∘-resp-≈ D.∘-resp-≈
  }
  where module C = Category C
        module D = Category D
        module F = Functor F
        module G = Functor G
        module E = Category E

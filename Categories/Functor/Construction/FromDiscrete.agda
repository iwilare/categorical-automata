{-# OPTIONS --without-K --safe #-}
open import Categories.Category.Core using (Category)

-- You can transform functions out of discrete
-- categories into functors.
module Categories.Functor.Construction.FromDiscrete {o β e} (π : Category o β e) where

open import Relation.Binary.PropositionalEquality.Core as β‘

open import Categories.Category.Construction.StrictDiscrete using (Discrete)
open import Categories.Functor.Core using (Functor)

open Category π
open Equiv

FromDiscrete : β {o} {A : Set o} β (A β Obj) β Functor (Discrete A) π
FromDiscrete {o} {A = A} select = record
  { Fβ = select
  ; Fβ = Ξ» { β‘.refl β id }
  ; identity = Equiv.refl
  ; homomorphism = Ξ» { {_} {_} {_} {β‘.refl} {β‘.refl} β Equiv.sym identityΒ² }
  ; F-resp-β = Ξ» { β‘.refl β Equiv.refl }
  }

{-# OPTIONS --without-K --safe #-}

-- Formalization of internal relations
-- (=congruences: https://ncatlab.org/nlab/show/congruence)

open import Categories.Category.Core using (Category)

module Categories.Object.InternalRelation {o β e} (π : Category o β e) where

open import Level using (_β_; suc)
open import Data.Unit using (β€)
open import Data.Fin using (Fin; zero) renaming (suc to nzero)

import Categories.Morphism as Mor
import Categories.Morphism.Reasoning as MR

open import Categories.Diagram.Pullback using (Pullback)
open import Categories.Diagram.KernelPair using (KernelPair)
open import Categories.Category.Cartesian using (Cartesian)

open import Categories.Category.BinaryProducts π using (BinaryProducts; module BinaryProducts)

private
  module π = Category π

open Category π
open Mor π using (JointMono)

-- A relation is a span, "which is (-1)-truncated as a morphism into the cartesian product."
-- (https://ncatlab.org/nlab/show/span#correspondences)
isRelation : {X Y R : π.Obj} (f : R β X) (g : R β Y) β Set (o β β β e)
isRelation{X}{Y}{R} f g = JointMono
     (Fin 2)
     (Ξ»{zero β X; (nzero _) β Y})
     (Ξ»{zero β f; (nzero _) β g})

record Relation (X Y : π.Obj) : Set (suc (o β β β e)) where
  constructor rel
  field
    dom : π.Obj
    pβ : dom β X
    pβ : dom β Y
    relation : isRelation pβ pβ

record EqSpan {X R : π.Obj} (f : R β X) (g : R β X) : Set (suc (o β β β e)) where
  field
     RΓR : Pullback π f g

  module RΓR = Pullback RΓR renaming (P to dom)

  field
     refl  : X β R
     sym   : R β R
     trans : RΓR.dom β R

     is-reflβ : f β refl β id
     is-reflβ : g β refl β id

     is-symβ : f β sym β g
     is-symβ : g β sym β f

     is-transβ : f β trans β f β RΓR.pβ
     is-transβ : g β trans β g β RΓR.pβ

-- Internal equivalence
record Equivalence (X : π.Obj) : Set (suc (o β β β e)) where
  field
     R : Relation X X

  module R = Relation R

  field
    eqspan : EqSpan R.pβ R.pβ

-- move to properties?

module _ where
  open Pullback hiding (P)
  open π.Equiv

  -- the span obtained from a KP does need that it forms a pullback
  KPβEqSpan : {X Y : π.Obj} (f : X β Y) (kp : KernelPair π f) (p : Pullback π (pβ kp) (pβ kp)) β EqSpan (pβ kp) (pβ kp)
  KPβEqSpan f kp p = record
    { RΓR = p
    ; refl  = universal kp refl
    ; sym   = universal kp {_} {pβ kp}{pβ kp} (sym (commute kp))
    ; trans = universal kp {_} {pβ kp β pβ p}{pβ kp β pβ p} f-commute
    ; is-reflβ  = pββuniversalβhβ kp
    ; is-reflβ  = pββuniversalβhβ kp
    ; is-symβ   = pββuniversalβhβ kp
    ; is-symβ   = pββuniversalβhβ kp
    ; is-transβ = pββuniversalβhβ kp
    ; is-transβ = pββuniversalβhβ kp
    }
    where
    open π.HomReasoning
    open MR π
    f-commute : f β pβ kp β pβ p β f β pβ kp β pβ p
    f-commute = begin
      f β pβ kp β pβ p   ββ¨ pullΛ‘ (commute kp) β©
      (f β pβ kp) β pβ p ββ¨ pullΚ³ (sym (commute p)) β©
      f β pβ kp β pβ p   ββ¨ pullΛ‘ (commute kp) β©
      (f β pβ kp) β pβ p ββ¨ assoc β©
      f β pβ kp β pβ p   β

  -- but the induced relation does not
  KPβisRelation : {X Y : π.Obj} (f : X β Y) β (kp : KernelPair π f) β isRelation (pβ kp) (pβ kp)
  KPβisRelation f kp _ _ eq = unique-diagram kp (eq zero) (eq (nzero zero))

  KPβRelation : {X Y : π.Obj} (f : X β Y) β (kp : KernelPair π f) β Relation X X
  KPβRelation f kp = rel (Pullback.P kp) (pβ kp) (pβ kp) (KPβisRelation f kp)

  KPβEquivalence : {X Y : π.Obj} (f : X β Y) β (kp : KernelPair π f) (pb : Pullback π (pβ kp) (pβ kp)) β Equivalence X
  KPβEquivalence f kp pb = record { R = KPβRelation f kp ; eqspan = KPβEqSpan f kp pb }

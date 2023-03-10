{-# OPTIONS --without-K --safe #-}

{-
  Properties and definitions regarding Morphisms of a category:
  - Monomorphism
  - Epimorphism
  - Isomorphism
  - (object) equivalence ('spelled' _β_ ). Exported as the module β
-}
open import Categories.Category.Core

module Categories.Morphism {o β e} (π : Category o β e) where

open import Level
open import Relation.Binary hiding (_β_)

open import Categories.Morphism.Reasoning.Core π

open Category π

private
  variable
    A B C : Obj

Mono : β (f : A β B) β Set (o β β β e)
Mono {A = A} f = β {C} β (gβ gβ : C β A) β f β gβ β f β gβ β gβ β gβ

JointMono : {ΞΉ : Level} (I : Set ΞΉ) (B : I β Obj) β ((i : I) β A β B i) β Set (o β β β e β ΞΉ)
JointMono {A} I B f = β {C} β (gβ gβ : C β A) β ((i : I) β f i β gβ β f i β gβ) β gβ β gβ

record _β£_ (A B : Obj) : Set (o β β β e) where
  field
    mor  : A β B
    mono : Mono mor

Epi : β (f : A β B) β Set (o β β β e)
Epi {B = B} f = β {C} β (gβ gβ : B β C) β gβ β f β gβ β f β gβ β gβ

JointEpi : (I : Set) (A : I β Obj) β ((i : I) β A i β B) β Set (o β β β e)
JointEpi {B} I A f = β {C} β (gβ gβ : B β C) β ((i : I) β gβ β f i β gβ β f i) β gβ β gβ

record _β _ (A B : Obj) : Set (o β β β e) where
  field
    mor : A β B
    epi : Epi mor

_SectionOf_ : (g : B β A) (f : A β B) β Set e
g SectionOf f = f β g β id

_RetractOf_ : (g : B β A) (f : A β B) β Set e
g RetractOf f = g β f β id

record Retract (X U : Obj) : Set (β β e) where
  field
    section : X β U
    retract : U β X
    is-retract : retract β section β id

record Iso (from : A β B) (to : B β A) : Set e where
  field
    isoΛ‘ : to β from β id
    isoΚ³ : from β to β id

-- We often say that a morphism "is an iso" if there exists some inverse to it.
-- This does buck the naming convention we use somewhat, but it lines up
-- better with the literature.
record IsIso (from : A β B) : Set (β β e) where
  field
    inv : B β A
    iso : Iso from inv 

  open Iso iso public

infix 4 _β_
record _β_ (A B : Obj) : Set (β β e) where
  field
    from : A β B
    to   : B β A
    iso  : Iso from to

  open Iso iso public

-- don't pollute the name space too much
private
  β-refl : Reflexive _β_
  β-refl = record
    { from = id
    ; to   = id
    ; iso  = record
      { isoΛ‘ = identityΒ²
      ; isoΚ³ = identityΒ²
      }
    }

  β-sym : Symmetric _β_
  β-sym AβB = record
    { from = to
    ; to   = from
    ; iso  = record
      { isoΛ‘ = isoΚ³
      ; isoΚ³ = isoΛ‘
      }
    }
    where open _β_ AβB

  β-trans : Transitive _β_
  β-trans AβB BβC = record
    { from = from BβC β from AβB
    ; to   = to AβB β to BβC
    ; iso  = record
      { isoΛ‘ = begin
        (to AβB β to BβC) β from BβC β from AβB ββ¨ cancelInner (isoΛ‘ BβC) β©
        to AβB β from AβB                       ββ¨  isoΛ‘ AβB  β©
        id                                      β
      ; isoΚ³ = begin
        (from BβC β from AβB) β to AβB β to BβC ββ¨ cancelInner (isoΚ³ AβB) β©
        from BβC β to BβC                       ββ¨ isoΚ³ BβC β©
        id                                      β
      }
    }
    where open _β_
          open HomReasoning
          open Equiv

β-isEquivalence : IsEquivalence _β_
β-isEquivalence = record
  { refl  = β-refl
  ; sym   = β-sym
  ; trans = β-trans
  }

-- But make accessing it easy:
module β = IsEquivalence β-isEquivalence

β-setoid : Setoid _ _
β-setoid = record
  { Carrier       = Obj
  ; _β_           = _β_
  ; isEquivalence = β-isEquivalence
  }

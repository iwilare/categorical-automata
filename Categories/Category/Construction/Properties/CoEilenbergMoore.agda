{-# OPTIONS --without-K --safe #-}
-- verbatim dual of Categories.Category.Construction.Properties.EilenbergMoore
module Categories.Category.Construction.Properties.CoEilenbergMoore where

open import Level
import Relation.Binary.PropositionalEquality.Core as β‘

open import Categories.Adjoint
open import Categories.Adjoint.Properties
open import Categories.Category
open import Categories.Functor using (Functor; _βF_)
open import Categories.Functor.Equivalence
open import Categories.Comonad

open import Categories.NaturalTransformation.Core renaming (id to idN)
open import Categories.Morphism.HeterogeneousIdentity
open import Categories.Morphism.Reasoning

open import Categories.Adjoint.Construction.CoEilenbergMoore
open import Categories.Category.Construction.CoEilenbergMoore

private
  variable
    o β e : Level
    π π : Category o β e

module _ {F : Functor π π} {G : Functor π π} (Fβ£G : Adjoint F G) where
  private
    T : Comonad π
    T = adjointβcomonad Fβ£G

    coEMπ : Category _ _ _
    coEMπ = CoEilenbergMoore T

    module π = Category π
    module π = Category π
    module coEMπ = Category coEMπ

    open π.HomReasoning

    module T = Comonad T
    module F = Functor F
    module G = Functor G
    module FG = Functor (F βF G)

    open Adjoint Fβ£G
    open NaturalTransformation
    open Category.Equiv

  -- Maclane's Comparison Functor
  ComparisonF : Functor π coEMπ
  ComparisonF = record
   { Fβ = Ξ» X β record
    { A = F.Fβ X
    ; coaction = F.Fβ (unit.Ξ· X)
    ; commute = commute-obj
    ; identity = zig
    }
   ; Fβ = Ξ» {A} {B} f β record
    { arr = F.Fβ f
    ; commute = commute-mor
    }
   ; identity = F.identity
   ; homomorphism = F.homomorphism
   ; F-resp-β = F.F-resp-β
   }
   where
    commute-obj : {X : Category.Obj π} β T.F.Fβ (F.Fβ (unit.Ξ· X)) π.β F.Fβ (unit.Ξ· X) π.β T.Ξ΄.Ξ· (F.Fβ X) π.β F.Fβ (unit.Ξ· X)
    commute-obj {X} = begin
      F.Fβ (G.Fβ (F.Fβ (unit.Ξ· X))) π.β F.Fβ (unit.Ξ· X) ββ¨ sym π (F.homomorphism) β©
      F.Fβ (G.Fβ (F.Fβ (unit.Ξ· X)) π.β unit.Ξ· X)        ββ¨ Functor.F-resp-β F (unit.sym-commute (unit.Ξ· X)) β©
      F.Fβ (unit.Ξ· (G.Fβ (F.Fβ X)) π.β unit.Ξ· X)        ββ¨ F.homomorphism β©
      T.Ξ΄.Ξ· (F.Fβ X) π.β F.Fβ (unit.Ξ· X)                β
    commute-mor : {A B : Category.Obj π} {f : π [ A , B ]} β F.Fβ (unit.Ξ· B) π.β F.Fβ f π.β T.F.Fβ (F.Fβ f) π.β F.Fβ (unit.Ξ· A)
    commute-mor {A} {B} {f} = begin
     F.Fβ (unit.Ξ· B) π.β F.Fβ f          ββ¨ sym π (F.homomorphism) β©
     F.Fβ (unit.Ξ· B π.β f)               ββ¨ Functor.F-resp-β F (unit.commute f) β©
     F.Fβ (G.Fβ (F.Fβ f) π.β unit.Ξ· A)   ββ¨ F.homomorphism β©
     T.F.Fβ (F.Fβ f) π.β F.Fβ (unit.Ξ· A) β

  ComparisonβFβ‘Free : (ComparisonF βF G) β‘F Cofree T
  ComparisonβFβ‘Free = record
   { eqβ = Ξ» X β β‘.refl
   ; eqβ = Ξ» f β id-comm-sym π
   }

  ForgetfulβComparisonFβ‘G : (Forgetful T βF ComparisonF) β‘F F
  ForgetfulβComparisonFβ‘G = record
   { eqβ = Ξ» X β β‘.refl
   ; eqβ = Ξ» f β id-comm-sym π
   }
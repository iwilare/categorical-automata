{-# OPTIONS --without-K --safe #-}
-- verbatim dual of Categories.Category.Construction.Properties.Kleisli
module Categories.Category.Construction.Properties.CoKleisli where

open import Level
import Relation.Binary.PropositionalEquality as β‘

open import Categories.Adjoint
open import Categories.Adjoint.Properties
open import Categories.Category
open import Categories.Functor using (Functor; _βF_)
open import Categories.Functor.Equivalence
open import Categories.Comonad
import Categories.Morphism.Reasoning as MR

open import Categories.Adjoint.Construction.CoKleisli
open import Categories.Category.Construction.CoKleisli

private
  variable
    o β e : Level
    π π : Category o β e

module _ {F : Functor π π} {G : Functor π π} (Fβ£G : Adjoint F G) where
  private
    T : Comonad π
    T = adjointβcomonad Fβ£G

    πβ : Category _ _ _
    πβ = CoKleisli T

    module π = Category π
    module π = Category π
    module πβ = Category πβ


    module T = Comonad T
    module F = Functor F
    module G = Functor G

    open Adjoint Fβ£G

  -- Maclane's Comparison Functor
  ComparisonF : Functor πβ π
  ComparisonF = record
   { Fβ = Ξ» X β G.Fβ X
   ; Fβ = Ξ» {A} {B} f β π [ (G.Fβ f) β unit.Ξ· (G.Fβ A) ]
   ; identity = Ξ» {A} β zag
   ; homomorphism = Ξ» {X} {Y} {Z} {f} {g} β begin
      G.Fβ (g π.β F.Fβ (G.Fβ f) π.β F.Fβ (unit.Ξ· (G.Fβ X))) π.β unit.Ξ· (G.Fβ X)             ββ¨ pushΛ‘ G.homomorphism β©
      G.Fβ g π.β G.Fβ ((F.Fβ (G.Fβ f)) π.β F.Fβ (unit.Ξ· (G.Fβ X))) π.β unit.Ξ· (G.Fβ X)      ββ¨ (reflβ©ββ¨ pushΛ‘ G.homomorphism) β©
      G.Fβ g π.β G.Fβ (F.Fβ (G.Fβ f)) π.β G.Fβ (F.Fβ (unit.Ξ· (G.Fβ X))) π.β unit.Ξ· (G.Fβ X) ββ¨ (reflβ©ββ¨ (reflβ©ββ¨ sym (unit.commute (unit.Ξ· (G.Fβ X))))) β©
      G.Fβ g π.β G.Fβ (F.Fβ (G.Fβ f)) π.β unit.Ξ· (G.Fβ (F.Fβ (G.Fβ X))) π.β unit.Ξ· (G.Fβ X) ββ¨ (reflβ©ββ¨ pullΛ‘ (sym (unit.commute (G.Fβ f)))) β©
      G.Fβ g π.β (unit.Ξ· (G.Fβ Y) π.β G.Fβ f) π.β unit.Ξ· (G.Fβ X)                           ββ¨ MR.assocΒ²'' π β©
      (G.Fβ g π.β unit.Ξ· (G.Fβ Y)) π.β G.Fβ f π.β unit.Ξ· (G.Fβ X)                           β
   ; F-resp-β = Ξ» eq β π.β-resp-β (G.F-resp-β eq) (Category.Equiv.refl π)
   }
   where
    open π.HomReasoning
    open π.Equiv
    open MR π

  private
    L = ComparisonF
    module L = Functor L
    module Gβ = Functor (Forgetful T)
    module Fβ = Functor (Cofree T)

  FβLβ‘Forgetful : (F βF L) β‘F Forgetful T
  FβLβ‘Forgetful = record
   { eqβ = Ξ» X β β‘.refl
   ; eqβ = eq-1
   }
   where
   open π.HomReasoning
   open MR π
   eq-1 : {X Y : π.Obj} (f : F.Fβ (G.Fβ X) π.β Y) β π.id π.β F.Fβ (G.Fβ f π.β unit.Ξ· (G.Fβ X)) π.β (F.Fβ (G.Fβ f) π.β F.Fβ (unit.Ξ· (G.Fβ X))) π.β π.id
   eq-1 {X} {Y} f = begin
    π.id π.β F.Fβ (G.Fβ f π.β unit.Ξ· (G.Fβ X))          ββ¨ id-comm-sym β©
    F.Fβ (G.Fβ f π.β unit.Ξ· (G.Fβ X)) π.β π.id          ββ¨ (F.homomorphism β©ββ¨refl) β©
    (F.Fβ (G.Fβ f) π.β F.Fβ (unit.Ξ· (G.Fβ X))) π.β π.id β

  LβCofreeβ‘G : (L βF Cofree T) β‘F G
  LβCofreeβ‘G = record
   { eqβ = Ξ» X β β‘.refl
   ; eqβ = eq-1
   }
   where
   open π.HomReasoning
   open MR π
   eq-1 : {X Y : π.Obj} (f : X π.β Y) β π.id π.β G.Fβ (f π.β counit.Ξ· X) π.β unit.Ξ· (G.Fβ X) π.β G.Fβ f π.β π.id
   eq-1 {X} {Y} f = begin
    π.id π.β G.Fβ (f π.β counit.Ξ· X) π.β unit.Ξ· (G.Fβ X)         ββ¨ id-comm-sym β©
    (G.Fβ (f π.β counit.Ξ· X) π.β unit.Ξ· (G.Fβ X)) π.β π.id       ββ¨ (pushΛ‘ G.homomorphism β©ββ¨refl) β©
    (G.Fβ f π.β G.Fβ (counit.Ξ· X) π.β unit.Ξ· (G.Fβ X)) π.β π.id  ββ¨ (elimΚ³ zag β©ββ¨refl) β©
    G.Fβ f π.β π.id                                              β
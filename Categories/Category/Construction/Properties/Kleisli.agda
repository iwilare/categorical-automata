{-# OPTIONS --without-K --safe #-}
module Categories.Category.Construction.Properties.Kleisli where

open import Level
import Relation.Binary.PropositionalEquality as β‘

open import Categories.Adjoint
open import Categories.Adjoint.Properties
open import Categories.Category
open import Categories.Functor using (Functor; _βF_)
open import Categories.Functor.Equivalence
open import Categories.Monad
import Categories.Morphism.Reasoning as MR

open import Categories.Adjoint.Construction.Kleisli
open import Categories.Category.Construction.Kleisli

private
  variable
    o β e : Level
    π π : Category o β e

module _ {F : Functor π π} {G : Functor π π} (Fβ£G : Adjoint F G) where
  private
    T : Monad π
    T = adjointβmonad Fβ£G

    πβ : Category _ _ _
    πβ = Kleisli T

    module π = Category π
    module π = Category π
    module πβ = Category πβ


    module T = Monad T
    module F = Functor F
    module G = Functor G

    open Adjoint Fβ£G

  -- Maclane's Comparison Functor
  ComparisonF : Functor πβ π
  ComparisonF = record
    { Fβ = Ξ» X β F.Fβ X
    ; Fβ = Ξ» {A} {B} f β π [ counit.Ξ· (F.Fβ B) β F.Fβ f ]
    ; identity = zig
    ; homomorphism = Ξ» {X} {Y} {Z} {f} {g} β begin
      π [ counit.Ξ· (F.Fβ Z) β F.Fβ (π [ π [ G.Fβ (counit.Ξ· (F.Fβ Z)) β G.Fβ (F.Fβ g)] β f ])]                 ββ¨ reflβ©ββ¨ F.homomorphism β©
      π [ counit.Ξ· (F.Fβ Z) β π [ F.Fβ (π [ G.Fβ (counit.Ξ· (F.Fβ Z)) β G.Fβ (F.Fβ g) ]) β F.Fβ f ] ]          ββ¨ reflβ©ββ¨ F.homomorphism  β©ββ¨refl β©
      π [ counit.Ξ· (F.Fβ Z) β π [ π [ F.Fβ (G.Fβ (counit.Ξ· (F.Fβ Z))) β F.Fβ (G.Fβ (F.Fβ g)) ] β F.Fβ f ] ]   ββ¨ centerβ»ΒΉ refl refl β©
      π [ π [ counit.Ξ· (F.Fβ Z) β F.Fβ (G.Fβ (counit.Ξ· (F.Fβ Z))) ] β π [ F.Fβ (G.Fβ (F.Fβ g)) β F.Fβ f ] ]   ββ¨ counit.commute (counit.Ξ· (F.Fβ Z)) β©ββ¨refl β©
      π [ π [ counit.Ξ· (F.Fβ Z) β (counit.Ξ· (F.Fβ (G.Fβ (F.Fβ Z)))) ] β π [ F.Fβ (G.Fβ (F.Fβ g)) β F.Fβ f ] ] ββ¨ extendΒ² (counit.commute (F.Fβ g))  β©
      π [ π [ counit.Ξ· (F.Fβ Z) β F.Fβ g ] β π [ counit.Ξ· (F.Fβ Y) β F.Fβ f ] ]                               β
    ; F-resp-β = Ξ» eq β π.β-resp-βΚ³ (F.F-resp-β eq)
    }
    where
      open π.HomReasoning
      open π.Equiv
      open MR π

  private
    L = ComparisonF
    module L = Functor L
    module Gβ = Functor (Forgetful T)
    module Fβ = Functor (Free T)

  GβLβ‘Forgetful : (G βF L) β‘F Forgetful T
  GβLβ‘Forgetful = record
    { eqβ = Ξ» X β β‘.refl
    ; eqβ = Ξ» {A} {B} f β begin
      π [ π.id β G.Fβ (π [ counit.Ξ· (F.Fβ B) β F.Fβ f ]) ]        ββ¨ π.identityΛ‘ β©
      G.Fβ (π [ counit.Ξ· (F.Fβ B) β F.Fβ f ])                      ββ¨ G.homomorphism β©
      π [ G.Fβ (counit.Ξ· (F.Fβ B)) β G.Fβ (F.Fβ f) ]               βΛβ¨ π.identityΚ³ β©
      π [ π [ G.Fβ (counit.Ξ· (F.Fβ B)) β G.Fβ (F.Fβ f) ] β π.id ] β

    }
    where
      open π.HomReasoning

  LβFreeβ‘F : (L βF Free T) β‘F F
  LβFreeβ‘F = record
    { eqβ = Ξ» X β β‘.refl
    ; eqβ = Ξ» {A} {B} f β begin
      π [ π.id β π [ counit.Ξ· (F.Fβ B) β F.Fβ (π [ unit.Ξ· B β f ]) ] ] ββ¨ π.identityΛ‘ β©
      π [ counit.Ξ· (F.Fβ B) β F.Fβ (π [ unit.Ξ· B β f ]) ]               ββ¨ pushΚ³ F.homomorphism β©
      π [ π [ counit.Ξ· (F.Fβ B) β F.Fβ (unit.Ξ· B) ] β F.Fβ f ]          ββ¨ elimΛ‘ zig β©
      F.Fβ f                                                              βΛβ¨ π.identityΚ³ β©
      π [ F.Fβ f β π.id ]                                               β
    }
    where
      open π.HomReasoning
      open MR π

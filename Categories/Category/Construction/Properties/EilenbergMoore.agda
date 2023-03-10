{-# OPTIONS --without-K --safe #-}
module Categories.Category.Construction.Properties.EilenbergMoore where

open import Level
import Relation.Binary.PropositionalEquality.Core as β‘

open import Categories.Adjoint
open import Categories.Adjoint.Properties
open import Categories.Category
open import Categories.Functor using (Functor; _βF_)
open import Categories.Functor.Equivalence
open import Categories.Monad

open import Categories.NaturalTransformation.Core renaming (id to idN)
open import Categories.Morphism.HeterogeneousIdentity

open import Categories.Adjoint.Construction.EilenbergMoore
open import Categories.Category.Construction.EilenbergMoore

private
  variable
    o β e : Level
    π π : Category o β e

module _ {F : Functor π π} {G : Functor π π} (Fβ£G : Adjoint F G) where
  private
    T : Monad π
    T = adjointβmonad Fβ£G

    πα΅ : Category _ _ _
    πα΅ = EilenbergMoore T

    module π = Category π
    module π = Category π
    module πα΅ = Category πα΅

    open π.HomReasoning

    module T = Monad T
    module F = Functor F
    module G = Functor G

    open Adjoint Fβ£G
    open NaturalTransformation

  -- Maclane's Comparison Functor
  ComparisonF : Functor π πα΅
  ComparisonF = record
    { Fβ = Ξ» X β record
      { A = G.Fβ X
      ; action = G.Fβ (counit.Ξ· X)
      ; commute = commute (G βΛ‘ counit) (counit.Ξ· X)
      ; identity = zag
      }
    ; Fβ = Ξ» {A} {B} f β record
      { arr = G.Fβ f
      ; commute =  begin
        π [ G.Fβ f β G.Fβ (counit.Ξ· A) ]               βΛβ¨ G.homomorphism β©
        G.Fβ (π [ f β (counit.Ξ· A) ])                  βΛβ¨ G.F-resp-β (counit.commute f) β©
        G.Fβ (π [ counit.Ξ· B β F.Fβ (G.Fβ f) ])        ββ¨ G.homomorphism  β©
        π [ G.Fβ (counit.Ξ· B) β G.Fβ (F.Fβ (G.Fβ f)) ] β
      }
    ; identity = G.identity
    ; homomorphism = G.homomorphism
    ; F-resp-β = G.F-resp-β
    }

  private
    K = ComparisonF
    module K = Functor K
    module Gα΅ = Functor (Forgetful T)
    module Fα΅ = Functor (Free T)

  ComparisonβFβ‘Free : (ComparisonF βF F) β‘F Free T
  ComparisonβFβ‘Free = record
    { eqβ = Ξ» X β β‘.refl
    ; eqβ = Ξ» {A} {B} f β begin
      Moduleβ.arr (πα΅ [ (hid πα΅ β‘.refl) β K.Fβ (F.Fβ f) ]) ββ¨ hid-refl πα΅ {A = K.Fβ (F.Fβ B)} β©ββ¨refl β©
      Moduleβ.arr (πα΅ [ πα΅.id β K.Fβ (F.Fβ f) ])           ββ¨ π.identityΛ‘ {f = Moduleβ.arr (K.Fβ (F.Fβ f))} β©
      Moduleβ.arr (K.Fβ (F.Fβ f))                          ββ¨ π.Equiv.refl β©
      Moduleβ.arr (Fα΅.Fβ f)                                 βΛβ¨ πα΅.identityΚ³ {f = Fα΅.Fβ f} β©
      Moduleβ.arr (πα΅ [ Fα΅.Fβ f β πα΅.id ])                 βΛβ¨ reflβ©ββ¨ hid-refl πα΅ {A = Fα΅.Fβ A} β©
      Moduleβ.arr (πα΅ [ Fα΅.Fβ f β (hid πα΅ β‘.refl) ])       β
    }

  ForgetfulβComparisonFβ‘G : (Forgetful T βF ComparisonF) β‘F G
  ForgetfulβComparisonFβ‘G = record
    { eqβ = Ξ» X β β‘.refl
    ; eqβ = Ξ» f β begin
      π [ (hid π β‘.refl) β (Gα΅.Fβ (K.Fβ f)) ] ββ¨ hid-refl π β©ββ¨refl β©
      π [ π.id β (Gα΅.Fβ (K.Fβ f)) ]           ββ¨ π.identityΛ‘ β©
      (Gα΅.Fβ (K.Fβ f))                         ββ¨ π.Equiv.refl β©
      G.Fβ f                                   βΛβ¨ π.identityΚ³ β©
      π [ G.Fβ fΒ β π.id ]                     βΛβ¨ reflβ©ββ¨ hid-refl π β©
      π [ G.Fβ fΒ β (hid π β‘.refl) ]           β
    }

{-# OPTIONS --without-K --safe #-}

open import Categories.Category using (Category; module Commutation)
open import Categories.Category.Cartesian using (Cartesian)

-- Defines the following properties of a Category:
-- Cartesian.SymmetricMonoidal
--    a Cartesian category is Symmetric Monoidal if its induced monoidal structure is symmetric

module Categories.Category.Cartesian.SymmetricMonoidal {o β e} (π : Category o β e) (cartesian : Cartesian π) where

open import Data.Product using (_,_)

open Category π
open Commutation π
open HomReasoning

open import Categories.Category.BinaryProducts π using (module BinaryProducts)
open import Categories.Category.Cartesian.Monoidal using (module CartesianMonoidal)
open import Categories.Category.Monoidal using (Monoidal)
import Categories.Category.Monoidal.Symmetric as Sym

open import Categories.NaturalTransformation using (ntHelper)

private
  variable
    W X Y Z : Obj

open Cartesian cartesian using (products)
open CartesianMonoidal cartesian using (monoidal)
open Sym monoidal using (Symmetric; symmetricHelper)
open Monoidal monoidal using (_ββ_; _ββ_; module associator)
open BinaryProducts products

private
  B : β {X Y} β X ββ Y β Y ββ X
  B = swap

hexagon : [ (X ββ Y) ββ Z β Y ββ Z ββ X ]β¨
            B  ββ id                    ββ¨ (Y ββ X) ββ Z β©
            associator.from             ββ¨ Y ββ X ββ Z β©
            id ββ B
          β associator.from             ββ¨ X ββ Y ββ Z β©
            B                           ββ¨ (Y ββ Z) ββ X β©
            associator.from
          β©
hexagon = begin
      id ββ swap β assocΛ‘ β swap ββ id                        ββ¨ reflβ©ββ¨ reflβ©ββ¨ β¨β©-congΚ³ β¨β©β β©
      id ββ swap β assocΛ‘ β β¨ β¨ Οβ β Οβ , Οβ β Οβ β© , id β Οβ β© ββ¨ reflβ©ββ¨ assocΛ‘ββ¨β© β©
      id ββ swap β β¨ Οβ β Οβ , β¨ Οβ β Οβ , id β Οβ β© β©          ββ¨ βββ¨β© β©
      β¨ id β Οβ β Οβ , swap β β¨ Οβ β Οβ , id β Οβ β© β©           ββ¨ β¨β©-congβ identityΛ‘ swapββ¨β© β©
      β¨ Οβ β Οβ , β¨ id β Οβ , Οβ β Οβ β© β©                       ββ¨ β¨β©-congΛ‘ (β¨β©-congΚ³ identityΛ‘) β©
      β¨ Οβ β Οβ , β¨ Οβ , Οβ β Οβ β© β©                            βΛβ¨ assocΛ‘ββ¨β© β©
      assocΛ‘ β β¨ β¨ Οβ β Οβ , Οβ β© , Οβ β Οβ β©                   βΛβ¨ reflβ©ββ¨ swapββ¨β© β©
      assocΛ‘ β swap β assocΛ‘                                    β

symmetric : Symmetric
symmetric = symmetricHelper record
  { braiding    = record
    { FβG = ntHelper record
      { Ξ·       = Ξ» _ β swap
      ; commute = Ξ» _ β swapββ
      }
    ; FβG = ntHelper record
      { Ξ·       = Ξ» _ β swap
      ; commute = Ξ» _ β swapββ
      }
    ; iso = Ξ» _ β record
      { isoΛ‘ = swapβswap
      ; isoΚ³ = swapβswap
      }
    }
  ; commutative = swapβswap
  ; hexagon     = hexagon
  }

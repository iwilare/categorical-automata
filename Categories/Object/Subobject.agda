{-# OPTIONS --without-K --safe #-}

open import Categories.Category

module Categories.Object.Subobject {o β e} (π : Category o β e) where

open import Level
open import Data.Product
open import Data.Unit

open import Relation.Binary using (Poset)

open import Categories.Functor
open import Categories.Category.Slice
open import Categories.Category.SubCategory
open import Categories.Category.Construction.Thin
import Categories.Morphism as Mor
import Categories.Morphism.Reasoning as MR
open import Categories.Morphism.Notation

private
  module π = Category π

-- The Full Subcategory of the over category π/c on monomorphisms
slice-mono : π.Obj β Category _ _ _
slice-mono c = FullSubCategory (Slice π c) {I = Ξ£[ Ξ± β π.Obj ](Ξ± β£ c)} Ξ» (_ , i) β sliceobj (mor i)
  where open Mor π
        open _β£_

-- Poset of subobjects for some c β π
Subobjects : π.Obj β Poset _ _ _
Subobjects c = record
  { Carrier = παΆ.Obj
  ; _β_ = παΆ [_β_]
  ; _β€_ = παΆ [_,_]
  ; isPartialOrder = record
    { isPreorder = record
      { isEquivalence = Mor.β-isEquivalence παΆ
      ; reflexive = Ξ» iso β Mor._β_.from iso
      ; trans = Ξ» {(Ξ± , f) (Ξ² , g) (Ξ³ , h)} i j β slicearr (chase f g h i j)
      }
    ; antisym = Ξ» {(Ξ± , f) (Ξ² , g)} h i β record
      { from = h
      ; to = i
      ; iso = record
        { isoΛ‘ = mono f _ _ (chase f g f h i β βΊ π.identityΚ³)
        ; isoΚ³ = mono g _ _ (chase g f g i h β βΊ π.identityΚ³)
        }
      }
    }
  }
  where
    παΆ : Category _ _ _
    παΆ = slice-mono c

    module παΆ = Category παΆ

    open Mor π using (_β£_)
    open MR π
    open π.HomReasoning
    open _β£_

    chase : β {Ξ± Ξ² Ξ³ : π.Obj} (f : π [ Ξ± β£ c ]) (g : π [ Ξ² β£ c ]) (h : π [ Ξ³ β£ c ])
            β (i : παΆ [ (Ξ± , f) , (Ξ² , g) ]) β (j : παΆ [ (Ξ² , g) , (Ξ³ , h) ])
            β π [ π [ mor h β π [ Sliceβ.h j β Sliceβ.h i ] ] β mor f ]
    chase f g h i j = begin
      π [ mor h β π [ Sliceβ.h j β Sliceβ.h i ] ] ββ¨ pullΛ‘ (Sliceβ.β³ j)  β©
      π [ mor g β Sliceβ.h i ]                    ββ¨ Sliceβ.β³ i β©
      mor f β

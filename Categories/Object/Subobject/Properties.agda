{-# OPTIONS --without-K --safe #-}


module Categories.Object.Subobject.Properties where

open import Level
open import Data.Product
open import Data.Unit
open import Function using (_$_)

open import Relation.Binary using (_=[_]β_)
open import Relation.Binary.Bundles using (Poset)
open import Relation.Binary.Morphism.Bundles using (mkPosetHomo)

open import Categories.Category
open import Categories.Functor
open import Categories.Functor.Presheaf
open import Categories.Category.Slice
open import Categories.Object.Subobject
open import Categories.Diagram.Pullback renaming (glue to glue-pullback)
open import Categories.Diagram.Pullback.Properties
open import Categories.Category.Instance.Posets using (Posets)
open import Categories.Category.Instance.Setoids using (Setoids)
open import Categories.Adjoint.Instance.PosetCore using (Core)
import Categories.Morphism as Mor
import Categories.Morphism.Reasoning as MR
open import Categories.Morphism.Notation


module _ {o β e} {π : Category o β e} (has-pullbacks : β {A B X} β (f : π [ A , X ]) β (g : π [ B , X ]) β Pullback π f g) where
  private
    module π = Category π

  open π.HomReasoning
  open π.Equiv

  open Mor π
  open MR π
  open _β£_

  -- The Subobject functor, into the category of posets
  Subβ : Presheaf π (Posets (o β β β e) (β β e) (β β e))
  Subβ = record
    { Fβ = Subobjects π
    ; Fβ = Ξ» f β mkPosetHomo _ _ (morphism f) (Ξ» {(Ξ± , m) (Ξ² , n)} h β monotone f {Ξ± , m} {Ξ² , n} h)
    ; identity = Ξ» {A} {(Ξ± , m)} β
      let pid = has-pullbacks π.id (mor m)
      in record
        { from = record
          { h = Pullback.pβ pid
          ; β³ = βΊ (Pullback.commute pid) β π.identityΛ‘
          }
        ; to = record
          { h = Pullback.universal pid id-comm-sym
          ; β³ = Pullback.pββuniversalβhβ pid
          }
        ; iso = record
          { isoΛ‘ = pullback-identity π pid
          ; isoΚ³ = Pullback.pββuniversalβhβ pid
          }
        }
    ; homomorphism = Ξ» {X} {Y} {Z} {f} {g} {(Ξ± , m)} β
      let pfg = has-pullbacks (π [ f β g ]) (mor m)
          pf = has-pullbacks f (mor m)
          pg = has-pullbacks g (Pullback.pβ pf)
          iso = up-to-iso π pfg (glue-pullback π pf pg)
          module iso = _β_ iso
      in record
        { from = record
          { h = iso.from
          ; β³ = Pullback.pββuniversalβhβ pg
          }
        ; to = record
          { h = iso.to
          ; β³ = Pullback.pββuniversalβhβ pfg
          }
        ; iso = record
          { isoΛ‘ = iso.isoΛ‘
          ; isoΚ³ = iso.isoΚ³
          }
        }
    ; F-resp-β = Ξ» {A B f g} eq {(Ξ± , m)} β
      let pf = has-pullbacks f (mor m)
          pg = has-pullbacks g (mor m)
          iso = up-to-iso π pf (pullback-resp-β π pg (sym eq) refl)
          module iso = _β_ iso
      in record
        { from = record
          { h = iso.from
          ; β³ = Pullback.pββuniversalβhβ pg
          }
        ; to = record
          { h = iso.to
          ; β³ = Pullback.pββuniversalβhβ pf
          }
        ; iso = record
          { isoΛ‘ = iso.isoΛ‘
          ; isoΚ³ = iso.isoΚ³
          }
        }
    }
    where
      morphism : β {A B} β (f : π [ B , A ]) β Ξ£[ Ξ± β π.Obj ] (Ξ± β£ A) β Ξ£[ Ξ² β π.Obj ] (Ξ² β£ B)
      morphism f (Ξ± , m) = 
        let pb = has-pullbacks f (mor m)
        in Pullback.P pb , record
          { mor = Pullback.pβ pb
          ; mono = Pullback-resp-Mono π pb (mono m)
          }

      monotone : β {A B} (f : π [ B , A ]) β Poset._β€_ (Subobjects π A) =[ morphism f ]β Poset._β€_ (Subobjects π B)
      monotone f {(Ξ± , m)} {(Ξ² , n)} h =
        let pm = has-pullbacks f (mor m)
            pn = has-pullbacks f (mor n)
        in record
          { h = Pullback.universal pn $ begin
              π [ f β Pullback.pβ pm ] ββ¨ Pullback.commute pm β©
              π [ mor m β Pullback.pβ pm ] ββ¨ pushΛ‘ (βΊ (Sliceβ.β³ h)) β©
              π [ mor n β π [ Sliceβ.h h β Pullback.pβ pm ] ] β
          ; β³ = Pullback.pββuniversalβhβ pn
          }

  -- The subobject functor as a presheaf on Setoids.
  -- This is just Subβ composed with the 'Core'
  Sub : Presheaf π (Setoids (o β β β e) (β β e))
  Sub =  Core βF Subβ

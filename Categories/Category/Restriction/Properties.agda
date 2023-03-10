{-# OPTIONS --without-K --safe #-}

-- Some properties of Restriction Categories

-- The first few lemmas are from Cocket & Lack, Lemma 2.1 and 2.2
module Categories.Category.Restriction.Properties where

open import Data.Product using (Ξ£; _,_)
open import Level using (Level; _β_)

open import Categories.Category.Core using (Category)
open import Categories.Category.Restriction using (Restriction)
open import Categories.Category.SubCategory
open import Categories.Morphism using (Mono)
open import Categories.Morphism.Idempotent using (Idempotent)
open import Categories.Morphism.Properties using (Mono-id)
import Categories.Morphism.Reasoning as MR

module _ {o β e : Level} {π : Category o β e} (R : Restriction π) where
  open Category π
  open Restriction R
  open HomReasoning
  open MR π using (elimΛ‘; introΚ³)

  private
    variable
      A B C : Obj
      f : A β B
      g : B β C

  βf-idempotent : (A β B) β Idempotent π A
  βf-idempotent f = record { idem = f β ; idempotent = βΊ β-denestΚ³ β β-cong pidΚ³ }

  -- a special version of β being a partial left identity
  β-pidΛ‘-gf : f β β (g β f) β β (g β f) β
  β-pidΛ‘-gf {f = f} {g = g} = begin
    f β β (g β f) β   ββ¨ β-comm β©
    (g β f) β β f β   βΛβ¨ β-denestΚ³ β©
    ((g β f) β f β) β ββ¨ β-cong assoc β©
    (g β (f β f β)) β ββ¨ β-cong (β-resp-βΚ³ pidΚ³) β©
    (g β f) β β

  -- left denesting looks different in its conclusion
  β-denestΛ‘ : (g β β f) β β (g β f) β
  β-denestΛ‘ {g = g} {f = f} = begin
    (g β β f) β       ββ¨ β-cong β-skew-comm β©
    (f β (g β f) β) β ββ¨ β-denestΚ³ β©
    f β β (g β f) β   ββ¨ β-pidΛ‘-gf β©
    (g β f) β         β

  β-idempotent : f β β β f β
  β-idempotent {f = f} = begin
    f β β        βΛβ¨ β-cong identityΚ³ β©
    (f β β id) β ββ¨ β-denestΛ‘ β©
    (f β id) β   ββ¨ β-cong identityΚ³ β©
    f β β

  ββdenest : (g β β f β) β β g β β f β
  ββdenest {g = g} {f = f} = begin
    (g β β f β) β ββ¨ β-denestΚ³ β©
    g β β β f β   ββ¨ (β-idempotent β©ββ¨refl) β©
    g β β f β β

  Monoβfββid : Mono π f β f β β id
  Monoβfββid {f = f} mono = mono (f β) id (pidΚ³ β βΊ identityΚ³)

  -- if the domain of g is at least that of f, then the restriction coincides
  ββββ : f β g β β f β f β β f β β g β
  ββββ {f = f} {g = g} fgββf = βΊ (β-cong fgββf) β β-denestΚ³

  MonoβTotal : Mono π f β total f
  MonoβTotal = Monoβfββid

  β-pres-total : {A B C : Obj} {f : B β C} {g : A β B} β total f β total g β total (f β g)
  β-pres-total {f = f} {g = g} tf tg = begin
    (f β g) β   βΛβ¨ β-denestΛ‘ β©
    (f β β g) β ββ¨ β-cong (elimΛ‘ tf) β©
    g β         ββ¨ tg β©
    id β

  total-gfβtotal-f : total (g β f) β total f
  total-gfβtotal-f {g = g} {f = f} tgf = begin
    f β             ββ¨ introΚ³ tgf β©
    f β β (g β f) β ββ¨ β-pidΛ‘-gf β©
    (g β f) β       ββ¨ tgf β©
    id              β

  total-SubCat : SubCat π Obj
  total-SubCat = record
    { U = Ξ» x β x
    ; R = total
    ; Rid = MonoβTotal (Mono-id π)
    ; _βR_ = β-pres-total
    }

  Total : Category o (β β e) e
  Total = SubCategory π total-SubCat

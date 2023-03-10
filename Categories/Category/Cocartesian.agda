{-# OPTIONS --without-K --safe #-}

open import Categories.Category.Core using (Category)

-- BinaryCoproducts -- a category with all binary coproducts
-- Cocartesian -- a category with all coproducts

-- since most of the work is dual to Categories.Category.Cartesian, so the idea
-- in this module is to make use of duality
module Categories.Category.Cocartesian {o โ e} (๐ : Category o โ e) where

open import Level

private
  module ๐ = Category ๐
  open Category ๐
  open HomReasoning
  variable
    A B C D : Obj
    f g h i : A โ B

open import Categories.Category.BinaryProducts using (BinaryProducts)
open import Categories.Category.Cartesian ๐.op
open import Categories.Category.Cartesian.Monoidal using (module CartesianMonoidal)
import Categories.Category.Cartesian.SymmetricMonoidal as CSM
open import Categories.Category.Monoidal using (Monoidal)
open import Categories.Category.Monoidal.Symmetric
open import Categories.Morphism ๐
open import Categories.Morphism.Properties ๐
open import Categories.Morphism.Duality ๐
open import Categories.Morphism.Reasoning ๐
open import Categories.Object.Initial ๐ using (Initial)
open import Categories.Object.Coproduct ๐
open import Categories.Object.Duality ๐

open import Categories.Functor renaming (id to idF)
open import Categories.Functor.Properties
open import Categories.Functor.Bifunctor

record BinaryCoproducts : Set (levelOfTerm ๐) where

  infixr 6 _+_
  infixr 7 _+โ_

  field
    coproduct : โ {A B} โ Coproduct A B

  module coproduct {A} {B} = Coproduct (coproduct {A} {B})

  _+_ : Obj โ Obj โ Obj
  A + B = coproduct.A+B {A} {B}

  open coproduct
    using (iโ; iโ; [_,_]; injectโ; injectโ; []-congโ; โ-distribหก-[])
    renaming (unique to +-unique; ฮท to +-ฮท; g-ฮท to +-g-ฮท)
    public

  module Dual where
    op-binaryProducts : BinaryProducts op
    op-binaryProducts = record { product = CoproductโcoProduct coproduct }

    module op-binaryProducts = BinaryProducts op-binaryProducts

  open Dual

  +-comm : A + B โ B + A
  +-comm = op-โโโ (op-binaryProducts.ร-comm)

  +-assoc : A + B + C โ (A + B) + C
  +-assoc = op-โโโ (op-binaryProducts.ร-assoc)

  _+โ_ : A โ B โ C โ D โ A + C โ B + D
  _+โ_ = op-binaryProducts._โ_

  open op-binaryProducts
    using ()
    renaming ( โจโฉ-congสณ     to []-congสณ
             ; โจโฉ-congหก     to []-congหก
             ; assocหก       to +-assocสณ
             ; assocสณ       to +-assocหก
             ; swap         to +-swap
             ; first        to +-first
             ; second       to +-second
             ; ฯโโโ         to +โโiโ
             ; ฯโโโ         to +โโiโ
             ; โ-congโ      to +โ-congโ
             ; โโโจโฉ         to []โ+โ
             ; โโโ          to +โโ+โ
             ; โจโฉโ          to โ[]
             ; firstโsecond to +-secondโfirst
             ; swapโโ       to +โโ+-swap
             ; swapโswap    to +-swapโswap
             )
    public

  -- since op-ร- has type Bifunctor ๐.op ๐.op ๐.op,
  -- need to rewrap in order to type check
  -+- : Bifunctor ๐ ๐ ๐
  -+- = record
    { Fโ           = op-ร-.Fโ
    ; Fโ           = op-ร-.Fโ
    ; identity     = op-ร-.identity
    ; homomorphism = op-ร-.homomorphism
    ; F-resp-โ     = op-ร-.F-resp-โ
    }
    where op-ร- = op-binaryProducts.-ร-
          module op-ร- = Functor op-ร-

  -+_ : Obj โ Functor ๐ ๐
  -+_ = appสณ -+-

  _+- : Obj โ Functor ๐ ๐
  _+- = appหก -+-


record Cocartesian : Set (levelOfTerm ๐) where
  field
    initial    : Initial
    coproducts : BinaryCoproducts

  module initial    = Initial initial
  module coproducts = BinaryCoproducts coproducts

  open initial
    renaming (! to ยก; !-unique to ยก-unique; !-uniqueโ to ยก-uniqueโ)
    public
  open coproducts hiding (module Dual) public

  module Dual where
    open coproducts.Dual public

    op-cartesian : Cartesian
    op-cartesian = record
      { terminal = โฅโopโค initial
      ; products = op-binaryProducts
      }

    module op-cartesian = Cartesian op-cartesian

-- The op-cartesian structure induces a monoidal one.

module CocartesianMonoidal (cocartesian : Cocartesian) where
  open Cocartesian cocartesian
  private module op-cartesianMonoidal = CartesianMonoidal Dual.op-cartesian

  โฅ+AโA : โฅ + A โ A
  โฅ+AโA = op-โโโ (op-cartesianMonoidal.โครAโA)

  A+โฅโA : A + โฅ โ A
  A+โฅโA = op-โโโ (op-cartesianMonoidal.AรโคโA)

  open op-cartesianMonoidal
    using (monoidal)
    -- both are natural isomorphism
    renaming (โคร--id to โฅ+--id; -รโค-id to -+โฅ-id)
    public

  open Monoidal monoidal using (unit; unitorหก-commute-to; unitorหก-commute-from; unitorสณ-commute-to;
    unitorสณ-commute-from; assoc-commute-to; assoc-commute-from; triangle; pentagon)

  +-monoidal : Monoidal ๐
  +-monoidal = record
    { โ                    = -+-
    ; unit                 = unit
    ; unitorหก              = โฅ+AโA
    ; unitorสณ              = A+โฅโA
    ; associator           = โ.sym +-assoc
    ; unitorหก-commute-from = โบ unitorหก-commute-to
    ; unitorหก-commute-to   = โบ unitorหก-commute-from
    ; unitorสณ-commute-from = โบ unitorสณ-commute-to
    ; unitorสณ-commute-to   = โบ unitorสณ-commute-from
    ; assoc-commute-from   = โบ assoc-commute-to
    ; assoc-commute-to     = โบ assoc-commute-from
    -- the proof idea of triangle is that the opposite triangle is obtained for free,
    -- but notice that triangle and the opposite triangle form isomorphism.
    ; triangle             = ฮป {X Y} โ
                               Iso-โ triangle
                                     (Iso-โ ([ X +- ]-resp-Iso (Iso-swap (iso โฅ+AโA)))
                                            (iso +-assoc))
                                     ([ -+ Y ]-resp-Iso (Iso-swap (iso A+โฅโA)))
    ; pentagon             = ฮป {X Y Z W} โ
                               Iso-โ pentagon
                                     (Iso-โ ([ X +- ]-resp-Iso (iso +-assoc))
                                     (Iso-โ (iso +-assoc)
                                            ([ -+ W ]-resp-Iso (iso +-assoc))))
                                     (Iso-โ (iso +-assoc) (iso +-assoc))
    }
    where open op-cartesianMonoidal
          open _โ_

  open Monoidal +-monoidal public

module CocartesianSymmetricMonoidal (cocartesian : Cocartesian) where
  open Cocartesian cocartesian
  open CocartesianMonoidal cocartesian
  private
    module op-cartesianSymmetricMonoidal = CSM ๐.op Dual.op-cartesian

  +-symmetric : Symmetric +-monoidal
  +-symmetric = record
    { braided     = record
      { braiding = record
        { FโG = record
          { ฮท           = ฮป _ โ +-swap
          ; commute     = ฮป _ โ โบ +โโ+-swap
          ; sym-commute = ฮป _ โ +โโ+-swap
          }
        ; FโG = record
          { ฮท           = ฮป _ โ +-swap
          ; commute     = ฮป _ โ โบ +โโ+-swap
          ; sym-commute = ฮป _ โ +โโ+-swap
          }
        ; iso = ฮป _ โ iso +-comm
        }
      ; hexagonโ = hexagonโ
      ; hexagonโ = hexagonโ
      }
    ; commutative = commutative
    }
    where open op-cartesianSymmetricMonoidal
          open _โ_
          open Symmetric symmetric using (commutative; hexagonโ; hexagonโ)

  open Symmetric +-symmetric public

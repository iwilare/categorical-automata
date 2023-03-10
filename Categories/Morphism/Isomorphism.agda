{-# OPTIONS --without-K --safe #-}
open import Categories.Category

-- Mainly *properties* of isomorphisms, and a lot of other things too

-- TODO: split things up more semantically?

module Categories.Morphism.Isomorphism {o โ e} (๐ : Category o โ e) where

open import Level using (_โ_)
open import Function using (flip)

open import Data.Product using (_,_)
open import Relation.Binary using (Rel; _Preserves_โถ_; IsEquivalence)
open import Relation.Binary.Construct.Closure.Transitive
open import Relation.Binary.PropositionalEquality as โก using (_โก_)

import Categories.Category.Construction.Core as Core
open import Categories.Category.Groupoid using (IsGroupoid)
import Categories.Category.Groupoid.Properties as GroupoidProps
import Categories.Morphism as Morphism
import Categories.Morphism.Properties as MorphismProps
import Categories.Morphism.IsoEquiv as IsoEquiv
import Categories.Category.Construction.Path as Path

open Core ๐ using (Core; Core-isGroupoid; CoreGroupoid; module Shorthands)
open Morphism ๐
open MorphismProps ๐
open Path ๐

import Categories.Morphism.Reasoning as MR

open Category ๐
open Definitions ๐

private
  module MCore where
    open GroupoidProps CoreGroupoid public
    open MorphismProps Core         public
    open Morphism      Core         public
    open Path          Core         public

  variable
    A B C D E F : Obj

open Shorthands hiding (_โ_)

CommutativeIso = IsGroupoid.CommutativeSquare Core-isGroupoid

--------------------
-- Also stuff about transitive closure

โแตข-tc : A [ _โ_ ]โบ B โ A โ B
โแตข-tc = MCore.โ-tc

infix 4 _โโบ_
_โโบ_ : Rel (A [ _โ_ ]โบ B) e
_โโบ_ = MCore._โโบ_

TransitiveClosure : Category o (o โ โ โ e) e
TransitiveClosure = MCore.Path

--------------------
-- some infrastructure setup in order to say something about morphisms and isomorphisms
module _ where
  private
    data IsoPlus : A [ _โ_ ]โบ B โ Set (o โ โ โ e) where
      [_]     : {f : A โ B} {g : B โ A} โ Iso f g โ IsoPlus [ f ]
      _โผโบโจ_โฉ_ : โ A {fโบ : A [ _โ_ ]โบ B} {gโบ : B [ _โ_ ]โบ C} โ IsoPlus fโบ โ IsoPlus gโบ โ IsoPlus (_ โผโบโจ fโบ โฉ gโบ)

  open _โ_

  โโบโโโบ : A [ _โ_ ]โบ B โ A [ _โ_ ]โบ B
  โโบโโโบ [ f ]            = [ from f ]
  โโบโโโบ (_ โผโบโจ fโบ โฉ fโบโฒ) = _ โผโบโจ โโบโโโบ fโบ โฉ โโบโโโบ fโบโฒ

  reverse : A [ _โ_ ]โบ B โ B [ _โ_ ]โบ A
  reverse [ f ]            = [ โ.sym f ]
  reverse (_ โผโบโจ fโบ โฉ fโบโฒ) = _ โผโบโจ reverse fโบโฒ โฉ reverse fโบ

  reverseโโ-sym : (fโบ : A [ _โ_ ]โบ B) โ โแตข-tc (reverse fโบ) โก โ.sym (โแตข-tc fโบ)
  reverseโโ-sym [ f ]            = โก.refl
  reverseโโ-sym (_ โผโบโจ fโบ โฉ fโบโฒ)  = โก.congโ (Morphism.โ.trans ๐) (reverseโโ-sym fโบโฒ) (reverseโโ-sym fโบ)

  TransitiveClosure-groupoid : IsGroupoid TransitiveClosure
  TransitiveClosure-groupoid = record
    { _โปยน = reverse
    ; iso = ฮป {_ _ fโบ} โ record { isoหก = isoหกโฒ fโบ ; isoสณ = isoสณโฒ fโบ }
    }
    where
      open HomReasoningแตข

      isoหกโฒ : (fโบ : A [ _โ_ ]โบ B) โ โแตข-tc (reverse fโบ) โแตข โแตข-tc fโบ โแตข โ.refl
      isoหกโฒ fโบ = begin
          โแตข-tc (reverse fโบ) โแตข โแตข-tc fโบ
        โกโจ โก.cong (_โแตข โแตข-tc fโบ) (reverseโโ-sym fโบ) โฉ
          โ.sym (โแตข-tc fโบ) โแตข โแตข-tc fโบ
        โโจ โปยน-iso.isoหก โฉ
          โ.refl
        โ

      isoสณโฒ : (fโบ : A [ _โ_ ]โบ B) โ โแตข-tc fโบ โแตข โแตข-tc (reverse fโบ) โแตข โ.refl
      isoสณโฒ fโบ = begin
          โแตข-tc fโบ โแตข โแตข-tc (reverse fโบ)
        โกโจ โก.cong (โแตข-tc fโบ โแตข_) (reverseโโ-sym fโบ) โฉ
          โแตข-tc fโบ โแตข โ.sym (โแตข-tc fโบ)
        โโจ โปยน-iso.isoสณ โฉ
          โ.refl
        โ

  from-โแตข-tc : (fโบ : A [ _โ_ ]โบ B) โ from (โแตข-tc fโบ) โก โ-tc (โโบโโโบ fโบ)
  from-โแตข-tc [ f ]            = โก.refl
  from-โแตข-tc (_ โผโบโจ fโบ โฉ fโบโฒ) = โก.congโ _โ_ (from-โแตข-tc fโบโฒ) (from-โแตข-tc fโบ)

  โ*โโ*-cong : โโบโโโบ {A} {B} Preserves _โโบ_ โถ _โโบ_
  โ*โโ*-cong {_} {_} {fโบ} {gโบ} fโบโโบgโบ = begin
    โ-tc (โโบโโโบ fโบ)  โกหโจ from-โแตข-tc fโบ โฉ
    from (โแตข-tc fโบ)  โโจ from-โ fโบโโบgโบ โฉ
    from (โแตข-tc gโบ)  โกโจ from-โแตข-tc gโบ โฉ
    โ-tc (โโบโโโบ gโบ)  โ
    where open HomReasoning

  โ-shift : โ {fโบ : A [ _โ_ ]โบ B} {gโบ : B [ _โ_ ]โบ C} {hโบ : A [ _โ_ ]โบ C} โ
              (_ โผโบโจ fโบ โฉ  gโบ) โโบ hโบ โ gโบ โโบ (_ โผโบโจ reverse fโบ โฉ hโบ)
  โ-shift {fโบ = fโบ} {gโบ = gโบ} {hโบ = hโบ} eq = begin
    โแตข-tc gโบ                                      โโจ introสณ (I.isoสณ fโบ) โฉ
    โแตข-tc gโบ โแตข (โแตข-tc fโบ โแตข โแตข-tc (reverse fโบ))  โโจ pullหก eq โฉ
    โแตข-tc hโบ โแตข โแตข-tc (reverse fโบ)                โ
    where
      open HomReasoningแตข
      open MR Core
      module I {A B} (fโบ : A [ _โ_ ]โบ B) = Morphism.Iso (IsGroupoid.iso TransitiveClosure-groupoid {f = fโบ})

  lift : โ {fโบ : A [ _โ_ ]โบ B} โ IsoPlus fโบ โ A [ _โ_ ]โบ B
  lift [ iso ]            = [ record
    { from = _
    ; to   = _
    ; iso  = iso
    } ]
  lift (_ โผโบโจ iso โฉ isoโฒ) = _ โผโบโจ lift iso โฉ lift isoโฒ

  reduce-lift : โ {fโบ : A [ _โ_ ]โบ B} (fโฒ : IsoPlus fโบ) โ from (โแตข-tc (lift fโฒ)) โก โ-tc fโบ
  reduce-lift [ f ]           = โก.refl
  reduce-lift (_ โผโบโจ fโฒ โฉ fโณ) = โก.congโ _โ_ (reduce-lift fโณ) (reduce-lift fโฒ)

  lift-cong : โ {fโบ gโบ : A [ _โ_ ]โบ B} (fโฒ : IsoPlus fโบ) (gโฒ : IsoPlus gโบ) โ
              fโบ โโบ gโบ โ lift fโฒ โโบ lift gโฒ
  lift-cong {_} {_} {fโบ} {gโบ} fโฒ gโฒ eq = โ from-โโฒ โ
    where
      open HomReasoning

      from-โโฒ : from (โแตข-tc (lift fโฒ)) โ from (โแตข-tc (lift gโฒ))
      from-โโฒ = begin
        from (โแตข-tc (lift fโฒ))  โกโจ reduce-lift fโฒ โฉ
        โ-tc fโบ                 โโจ eq โฉ
        โ-tc gโบ                 โกหโจ reduce-lift gโฒ โฉ
        from (โแตข-tc (lift gโฒ))  โ

  lift-triangle : {f : A โ B} {g : C โ A} {h : C โ B} {k : B โ C} {i : B โ A} {j : A โ C} โ
    f โ g โ h โ (fโฒ : Iso f i) โ (gโฒ : Iso g j) โ (hโฒ : Iso h k) โ
    lift (_ โผโบโจ [ gโฒ ] โฉ [ fโฒ ]) โโบ lift [ hโฒ ]
  lift-triangle eq fโฒ gโฒ hโฒ = lift-cong (_ โผโบโจ [ gโฒ ] โฉ [ fโฒ ]) [ hโฒ ] eq

  lift-square : {f : A โ B} {g : C โ A} {h : D โ B} {i : C โ D} {j : D โ C} {a : B โ A} {b : A โ C} {c : B โ D} โ
    f โ g โ h โ i โ (fโฒ : Iso f a) โ (gโฒ : Iso g b) โ (hโฒ : Iso h c) โ (iโฒ : Iso i j) โ
    lift (_ โผโบโจ [ gโฒ ] โฉ [ fโฒ ]) โโบ lift (_ โผโบโจ [ iโฒ ] โฉ [ hโฒ ])
  lift-square eq fโฒ gโฒ hโฒ iโฒ = lift-cong (_ โผโบโจ [ gโฒ ] โฉ [ fโฒ ]) (_ โผโบโจ [ iโฒ ] โฉ [ hโฒ ]) eq

  lift-pentagon : {f : A โ B} {g : C โ A} {h : D โ C} {i : E โ B} {j : D โ E} {l : E โ D}
                  {a : B โ A} {b : A โ C} {c : C โ D} {d : B โ E} โ
    f โ g โ h โ i โ j โ
    (fโฒ : Iso f a) โ (gโฒ : Iso g b) โ (hโฒ : Iso h c) โ (iโฒ : Iso i d) โ (jโฒ : Iso j l) โ
    lift (_ โผโบโจ _ โผโบโจ [ hโฒ ] โฉ [ gโฒ ] โฉ [ fโฒ ]) โโบ lift (_ โผโบโจ [ jโฒ ] โฉ [ iโฒ ])
  lift-pentagon eq fโฒ gโฒ hโฒ iโฒ jโฒ = lift-cong (_ โผโบโจ _ โผโบโจ [ hโฒ ] โฉ [ gโฒ ] โฉ [ fโฒ ]) (_ โผโบโจ [ jโฒ ] โฉ [ iโฒ ]) eq

module _ where
  open _โ_

  -- projecting isomorphism commutations to morphism commutations

  project-triangle : {g : A โ B} {f : C โ A} {h : C โ B} โ g โแตข f โแตข h โ from g โ from f โ from h
  project-triangle = from-โ

  project-square : {g : A โ B} {f : C โ A} {i : D โ B} {h : C โ D} โ g โแตข f โแตข i โแตข h โ from g โ from f โ from i โ from h
  project-square = from-โ

  -- direct lifting from morphism commutations to isomorphism commutations

  lift-triangleโฒ : {f : A โ B} {g : C โ A} {h : C โ B} โ from f โ from g โ from h โ f โแตข g โแตข h
  lift-triangleโฒ = โ_โ

  lift-squareโฒ : {f : A โ B} {g : C โ A} {h : D โ B} {i : C โ D} โ from f โ from g โ from h โ from i โ f โแตข g โแตข h โแตข i
  lift-squareโฒ = โ_โ

  lift-pentagonโฒ : {f : A โ B} {g : C โ A} {h : D โ C} {i : E โ B} {j : D โ E} โ
                   from f โ from g โ from h โ from i โ from j โ f โแตข g โแตข h โแตข i โแตข j
  lift-pentagonโฒ = โ_โ

  open MR Core
  open HomReasoningแตข
  open MR.GroupoidR _ Core-isGroupoid

  squaresรโโโ : {f fโฒ : A โ B} {g : A โ C} {h : B โ D} {i iโฒ : C โ D} โ
                CommutativeIso f g h i โ CommutativeIso fโฒ g h iโฒ โ i โแตข iโฒ โ f โแตข fโฒ
  squaresรโโโ sqโ sqโ eq = MCore.isosรโโโ eq helperโ (MCore.โ.sym helperโ) sqโ sqโ
    where
      helperโ = record { iso = โปยน-iso }
      helperโ = record { iso = โปยน-iso }

  -- imagine a triangle prism, if all the sides and the top face commute, the bottom face commute.
  triangle-prism : {iโฒ : A โ B} {fโฒ : C โ A} {hโฒ : C โ B} {i : D โ E} {j : D โ A}
    {k : E โ B} {f : F โ D} {g : F โ C} {h : F โ E} โ
    iโฒ โแตข fโฒ โแตข hโฒ โ
    CommutativeIso i j k iโฒ โ CommutativeIso f g j fโฒ โ CommutativeIso h g k hโฒ โ
    i โแตข f โแตข h
  triangle-prism {iโฒ = iโฒ} {fโฒ} {_} {i} {_} {k} {f} {g} {_} eq sqโ sqโ sqโ =
    squaresรโโโ glued sqโ eq
    where
      glued : CommutativeIso (i โแตข f) g k (iโฒ โแตข fโฒ)
      glued = โบ (glue (โบ sqโ) (โบ sqโ))

  elim-triangleหก : {f : A โ B} {g : C โ A} {h : D โ C} {i : D โ B} {j : D โ A} โ
                   f โแตข g โแตข h โแตข i โ f โแตข j โแตข i โ g โแตข h โแตข j
  elim-triangleหก perim tri = MCore.mono _ _ (perim โ โบ tri)

  elim-triangleหกโฒ : {f : A โ B} {g : C โ A} {h : D โ C} {i : D โ B} {j : C โ B} โ
                    f โแตข g โแตข h โแตข i โ j โแตข h โแตข i โ f โแตข g โแตข j
  elim-triangleหกโฒ {f = f} {g} {h} {i} {j} perim tri = MCore.epi _ _ ( begin
    (f โแตข g) โแตข h โโจ โ assoc โ โฉ
    f โแตข g โแตข h   โโจ perim โฉ
    i             โหโจ tri โฉ
    j โแตข h        โ )

  cut-squareสณ : {g : A โ B} {f : A โ C} {h : B โ D} {i : C โ D} {j : B โ C} โ
                CommutativeIso g f h i โ i โแตข j โแตข h โ j โแตข g โแตข f
  cut-squareสณ {g = g} {f = f} {h = h} {i = i} {j = j} sq tri = begin
    j โแตข g            โโจ switch-fromtoหกโฒ {f = i} {h = j} {k = h} tri โฉโโจrefl โฉ
    (i โปยน โแตข h) โแตข g  โโจ โ assoc โ โฉ
    i โปยน โแตข h โแตข g    โหโจ switch-fromtoหกโฒ {f = i} {h = f} {k = h โแตข g} (โบ sq) โฉ
    f                 โ

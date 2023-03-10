{-# OPTIONS --without-K --safe #-}

-- Exact category (https://ncatlab.org/nlab/show/exact+category)
-- is a regular category
-- in which every internal equivalence is a kernel pair

module Categories.Category.Exact where

open import Level

open import Categories.Category.Core
open import Categories.Diagram.Pullback
open import Categories.Category.Cocartesian
open import Categories.Object.Coproduct
open import Categories.Morphism
open import Categories.Diagram.Coequalizer
open import Categories.Diagram.KernelPair

open import Categories.Category.Regular
open import Categories.Morphism.Regular

open import Categories.Object.InternalRelation

record Exact {o ā e : Level} (š : Category o ā e) : Set (suc (o ā ā ā e)) where
  open Category š
  open Pullback
  open Coequalizer
  open Equivalence

  field
    regular    : Regular š
    quotient   : ā {X : Obj} (E : Equivalence š X) ā Coequalizer š (R.pā E) (R.pā E)
    effective  : ā {X : Obj} (E : Equivalence š X) ā IsPullback š (R.pā E) (R.pā E)
      (arr (quotient E)) (arr (quotient E))

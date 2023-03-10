{-# OPTIONS --without-K --safe #-}

module Categories.Category.Regular where

-- https://ncatlab.org/nlab/show/regular+category
-- https://en.wikipedia.org/wiki/Regular_category

open import Level

open import Categories.Category.Core
open import Categories.Category.Complete.Finitely using (FinitelyComplete)
open import Categories.Diagram.Coequalizer
open import Categories.Diagram.KernelPair
open import Categories.Diagram.Pullback
open import Categories.Morphism.Regular

record Regular {o ā e : Level} (š : Category o ā e) : Set (suc (o ā ā ā e)) where
  open Category š
  open Pullback

  field
    finitely-complete : FinitelyComplete š
    coeq-of-kernelpairs : {A B : Obj} (f : A ā B) (kp : KernelPair š f) ā Coequalizer š (pā kp) (pā kp)
    pullback-of-regularepi-is-regularepi : {A B C : Obj} (f : B ā A) {g : C ā A} ā RegularEpi š f ā (p : Pullback š f g) ā RegularEpi š (pā p)

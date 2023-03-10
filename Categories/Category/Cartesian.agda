{-# OPTIONS --without-K --safe #-}

open import Categories.Category using (Category)

-- Defines the following properties of a Category:
-- Cartesian -- a Cartesian category is a category with all products

--  (for the induced Monoidal structure, see Cartesian.Monoidal)

module Categories.Category.Cartesian {o ā e} (š : Category o ā e) where

open import Level using (levelOfTerm)
open import Data.Nat using (ā; zero; suc)

open Category š
open HomReasoning

open import Categories.Category.BinaryProducts š using (BinaryProducts; module BinaryProducts)
open import Categories.Object.Terminal š using (Terminal)

private
  variable
    A B C D W X Y Z : Obj
    f fā² g gā² h i : A ā B

-- Cartesian monoidal category
record Cartesian : Set (levelOfTerm š) where
  field
    terminal : Terminal
    products : BinaryProducts
  open BinaryProducts products using (_Ć_)

  power : Obj ā ā ā Obj
  power A 0 = Terminal.ā¤ terminal
  power A 1 = A
  power A (suc (suc n)) = A Ć power A (suc n)

open import Level
open import Data.Unit
open import Data.Product
open import Data.Nat
open import Categories.Object.Terminal
open import Categories.Object.Product.Indexed
open import Categories.Object.Product
open import Categories.NaturalTransformation using (ntHelper)
open import Categories.Functor.Slice
open import Categories.Functor.Algebra
open import Categories.Functor renaming (id to idF)
open import Categories.Diagram.Pullback.Indexed
open import Categories.Diagram.Pullback
open import Categories.Category.Slice
open import Categories.Category.Construction.F-Algebras
open import Categories.Category.Construction.Comma
open import Categories.Category.Complete.Properties using (Complete⇒FinitelyComplete)
open import Categories.Category.Complete.Finitely using (FinitelyComplete)
open import Categories.Category.Complete using (Complete)
open import Categories.Category.BinaryProducts
open import Categories.Category
open import Categories.Adjoint
open Categories.Functor.Functor
import Function as Fun
import Categories.Morphism.Reasoning as MR
import Categories.Category.Complete

module PullbacksInCat {o l e} {C : Category o l e} {X : Functor C C} (O : Category.Obj C) where
  
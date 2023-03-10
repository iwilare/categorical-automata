{-# OPTIONS --without-K --safe #-}
module Categories.Functor.Limits where

open import Level

open import Categories.Category
open import Categories.Functor
open import Categories.Functor.Properties
open import Categories.Object.Terminal
open import Categories.Object.Initial

open import Categories.Diagram.Limit
open import Categories.Diagram.Colimit
open import Categories.Diagram.Cone.Properties
open import Categories.Diagram.Cocone.Properties

open import Categories.Category.Construction.Cones
open import Categories.Category.Construction.Cocones

private
  variable
    o β e : Level
    π π β : Category o β e

module _ (F : Functor π π) {J : Functor β π} where

  PreservesLimit : (L : Limit J) β Set _
  PreservesLimit L = IsTerminal (Cones (F βF J)) (F-map-ConeΛ‘ F limit)
    where open Limit L

  PreservesColimit : (L : Colimit J) β Set _
  PreservesColimit L = IsInitial (Cocones (F βF J)) (F-map-CoconeΛ‘ F colimit)
    where open Colimit L

  ReflectsLimits : Set _
  ReflectsLimits = β (K : Cone J) β IsTerminal (Cones (F βF J)) (F-map-ConeΛ‘ F K) β IsTerminal (Cones J) K

  ReflectsColimits : Set _
  ReflectsColimits = β (K : Cocone J) β IsInitial (Cocones (F βF J)) (F-map-CoconeΛ‘ F K) β IsInitial (Cocones J) K

--   record CreatesLimits : Set (o β β β e β oβ² β ββ² β eβ² β oβ³ β ββ³) where
--     field
--       preserves-limits : PreservesLimit
--       reflects-limits  : ReflectsLimits

--   record CreatesColimits : Set (o β β β e β oβ² β ββ² β eβ² β oβ³ β ββ³) where
--     field
--       preserves-colimits : PreservesColimit
--       reflects-colimits  : ReflectsColimits

Continuous : β o β e β (F : Functor π π) β Set _
Continuous {π = π} o β e F = β {π₯ : Category o β e} {J : Functor π₯ π} (L : Limit J) β PreservesLimit F L

Cocontinuous : β o β e β (F : Functor π π) β Set _
Cocontinuous {π = π} o β e F = β {π₯ : Category o β e} {J : Functor π₯ π} (L : Colimit J) β PreservesColimit F L

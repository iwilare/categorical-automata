{-# OPTIONS --without-K --safe #-}

open import Categories.Category.Core
open import Categories.Object.Terminal hiding (up-to-iso)

module Categories.Object.NaturalNumber {o β e} (π : Category o β e) (π-Terminal : Terminal π) where

open import Level

open import Categories.Morphism π
open import Categories.Morphism.Reasoning π

open Category π
open HomReasoning
open Equiv

open Terminal π-Terminal

private
  variable
    A B C D X Y Z : Obj
    h i j : A β B

record IsNaturalNumber (N : Obj) : Set (o β β β e) where
  field
    z : β€ β N
    s : N β N
    universal : β {A} β β€ β A β A β A β N β A
    z-commute : β {A} {q : β€ β A} {f : A β A} β q β universal q f β z
    s-commute : β {A} {q : β€ β A} {f : A β A} β f β universal q f β universal q f β s
    unique    : β {A} {q : β€ β A} {f : A β A} {u : N β A} β q β u β z β f β u β u β s β u β universal q f

  Ξ· : universal z s β id
  Ξ· = βΊ (unique (βΊ identityΛ‘) id-comm)

  universal-cong : β {A} β {f fβ² : β€ β A} β {g gβ² : A β A} β f β fβ² β g β gβ² β universal f g β universal fβ² gβ²
  universal-cong fβfβ² gβgβ² = unique (βΊ fβfβ² β  z-commute) (β-resp-βΛ‘ (βΊ gβgβ²) β s-commute)

record NaturalNumber : Set (o β β β e) where
  field
    N : Obj
    isNaturalNumber : IsNaturalNumber N

  open IsNaturalNumber isNaturalNumber public

open NaturalNumber

module _ (N : NaturalNumber) (Nβ² : NaturalNumber) where
  private
    module N = NaturalNumber N
    module Nβ² = NaturalNumber Nβ²

  up-to-iso : N.N β Nβ².N
  up-to-iso = record
    { from = N.universal Nβ².z Nβ².s
    ; to = Nβ².universal N.z N.s
    ; iso = record
      { isoΛ‘ = universal-β N Nβ²
      ; isoΚ³ = universal-β Nβ² N
      }
    }
    where
      universal-β : β (N Nβ² : NaturalNumber) β universal Nβ² (z N) (s N) β universal N (z Nβ²) (s Nβ²) β id  
      universal-β N Nβ² = unique N (z-commute Nβ² β pushΚ³ (z-commute N)) (pullΛ‘ (s-commute Nβ²) β assoc β β-resp-βΚ³ (s-commute N) β βΊ assoc) β (Ξ· N)
      

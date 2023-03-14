{-# OPTIONS --allow-unsolved-metas #-}

open import Level
open import Categories.Category
open import Categories.Object.Terminal
import Categories.Morphism.Reasoning as MR
open import Categories.Functor renaming (id to idF)
open import Categories.Category.Cartesian.Bundle
open import Categories.Category.BinaryProducts

module Mealy {o l e} (C : CartesianCategory o l e) where

open CartesianCategory C

open HomReasoning
open Terminal terminal
open BinaryProducts products
open import Categories.Morphism.Reasoning U
open import Categories.Morphism U

record MealyObj I O : Set (o ⊔ l ⊔ e) where
  field
    E : Obj
    d : E × I ⇒ E
    s : E × I ⇒ O

open MealyObj

record Mealy⇒ {I} {O} (X Y : MealyObj I O) : Set (o ⊔ l ⊔ e) where
  private
    module X = MealyObj X
    module Y = MealyObj Y
  field
    hom    : X.E ⇒ Y.E
    comm-d : hom ∘ X.d ≈ Y.d ∘ first hom
    comm-s : X.s ≈ Y.s ∘ first hom

open Mealy⇒

first-identity : ∀ {A C} → first {C = C} (id {A = A}) ≈ id
first-identity = ⟨⟩-cong₂ identityˡ identityˡ ○ η

Mealy : ∀ I O → Category (o ⊔ l ⊔ e) (o ⊔ l ⊔ e) e
Mealy I O = record
  { Obj = MealyObj I O
  ; _⇒_ = Mealy⇒
  ; _≈_ = λ f g → hom f ≈ hom g
  ; id = λ {A} → let module A = MealyObj A in
    record { hom = id
           ; comm-d = identityˡ ○ introʳ first-identity
           ; comm-s = introʳ first-identity
           }
  ; _∘_ = λ {A} {B} {C} g f →
    let
      module f = Mealy⇒ f
      module g = Mealy⇒ g
      module A = MealyObj A
      module B = MealyObj B
      module C = MealyObj C in record
    { hom = g.hom ∘ f.hom
    ; comm-d = begin (g.hom ∘ f.hom) ∘ A.d ≈⟨ pullʳ f.comm-d ⟩
                     g.hom ∘ B.d ∘ first f.hom ≈⟨ pullˡ g.comm-d ⟩
                     (C.d ∘ first g.hom) ∘ first f.hom ≈⟨ pullʳ first∘first ⟩
                     C.d ∘ first (g.hom ∘ f.hom) ∎
    ; comm-s = begin A.s ≈⟨ f.comm-s ⟩
                     B.s ∘ first f.hom ≈⟨ g.comm-s ⟩∘⟨refl ⟩
                     (C.s ∘ first g.hom) ∘ first f.hom ≈⟨ pullʳ first∘first ⟩
                     C.s ∘ first (g.hom ∘ f.hom) ∎
    }
  ; assoc = assoc
  ; sym-assoc = sym-assoc
  ; identityˡ = identityˡ
  ; identityʳ = identityʳ
  ; identity² = identity²
  ; equiv = record { refl = Equiv.refl ; sym = Equiv.sym ; trans = Equiv.trans }
  ; ∘-resp-≈ = ∘-resp-≈
  }

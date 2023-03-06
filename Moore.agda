{-# OPTIONS --allow-unsolved-metas #-}

open import Level
open import Categories.Category
open import Categories.Object.Terminal
import Categories.Morphism.Reasoning as MR
open import Categories.Functor renaming (id to idF)
open import Categories.Category.Cartesian.Bundle
open import Categories.Category.BinaryProducts

module Moore {o l e} (C : CartesianCategory o l e) where

open CartesianCategory C

open HomReasoning
open Terminal terminal
open BinaryProducts products
open import Categories.Morphism.Reasoning U
open import Categories.Morphism U

record MooreObj I O : Set (o ⊔ l ⊔ e) where
  field
    E : Obj
    d : E × I ⇒ E
    s : E ⇒ O

open MooreObj

record Moore⇒ {I} {O} (X Y : MooreObj I O) : Set (o ⊔ l ⊔ e) where
  private
    module X = MooreObj X
    module Y = MooreObj Y
  field
    hom    : X.E ⇒ Y.E
    comm-d : hom ∘ X.d ≈ Y.d ∘ first hom
    comm-s : X.s ≈ Y.s ∘ hom

open Moore⇒

Moore : ∀ I O → Category (o ⊔ l ⊔ e) (o ⊔ l ⊔ e) e
Moore I O = record
  { Obj = MooreObj I O
  ; _⇒_ = Moore⇒
  ; _≈_ = λ f g → hom f ≈ hom g
  ; id = λ {A} → let module A = MooreObj A in
    record { hom = id
           ; comm-d = identityˡ ○ introʳ
           first-identity
           ; comm-s = Equiv.sym identityʳ
           }
  ; _∘_ = λ {A} {B} {C} g f →
    let
      module f = Moore⇒ f
      module g = Moore⇒ g
      module A = MooreObj A
      module B = MooreObj B
      module C = MooreObj C in record
    { hom = g.hom ∘ f.hom
    ; comm-d = begin (g.hom ∘ f.hom) ∘ A.d ≈⟨ pullʳ f.comm-d ⟩
                    g.hom ∘ B.d ∘ first f.hom ≈⟨ pullˡ g.comm-d ⟩
                    (C.d ∘ first g.hom) ∘ first f.hom ≈⟨ pullʳ first∘first ⟩
                    C.d ∘ first (g.hom ∘ f.hom) ∎
    ; comm-s = begin A.s ≈⟨ f.comm-s ⟩
                    B.s ∘ f.hom ≈⟨ g.comm-s ⟩∘⟨refl ⟩
                    (C.s ∘ g.hom) ∘ f.hom ≈⟨ assoc ⟩
                    C.s ∘ (g.hom ∘ f.hom) ∎
    }
  ; assoc = assoc
  ; sym-assoc = sym-assoc
  ; identityˡ = identityˡ
  ; identityʳ = identityʳ
  ; identity² = identity²
  ; equiv = record { refl = Equiv.refl ; sym = Equiv.sym ; trans = Equiv.trans }
  ; ∘-resp-≈ = ∘-resp-≈
  }

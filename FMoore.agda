open import Level
open import Categories.Category
open import Categories.Functor renaming (id to idF)
open Categories.Functor.Functor
import Categories.Morphism.Reasoning as MR
import Categories.Category.Complete
open import Categories.Category.Complete using (Complete)
open import Categories.Category.Complete.Finitely using (FinitelyComplete)
open import Categories.Category.Complete.Properties using (Complete⇒FinitelyComplete)
open import Categories.Category.BinaryProducts
open import Categories.Object.Product.Indexed
open import Categories.Object.Product
open import Categories.Object.Terminal
open import Categories.Diagram.Pullback
open import Categories.Adjoint
open import Data.Nat using (ℕ; suc; zero)
open import Relation.Binary.PropositionalEquality

module FMoore {o l e} {C : Category o l e} (F : Functor C C) (O : Category.Obj C) where

open Category C
open HomReasoning
open MR C

private
  module F = Functor F

record FMooreObj : Set (o ⊔ l) where
  field
    E : Obj
    d : F.F₀ E ⇒ E
    s : E ⇒ O

open FMooreObj public

record FMoore⇒ (A B : FMooreObj) : Set (o ⊔ l ⊔ e) where
  private
    module A = FMooreObj A
    module B = FMooreObj B
  field
    hom    : A.E ⇒ B.E
    comm-d : hom ∘ A.d ≈ B.d ∘ F.₁ hom
    comm-s : A.s ≈ B.s ∘ hom

open FMoore⇒ public

_⊚_ : {A B C : FMooreObj} → FMoore⇒ B C → FMoore⇒ A B → FMoore⇒ A C
_⊚_ {A} {B} {C} g f = record
  { hom = hom g ∘ hom f
  ; comm-d = begin
               (g.hom ∘ f.hom) ∘ d A       ≈⟨ pullʳ f.comm-d ⟩
               g.hom ∘ d B ∘ F.₁ f.hom     ≈⟨ extendʳ g.comm-d ⟩
               d C ∘ F.₁ g.hom ∘ F.₁ f.hom ≈⟨ refl⟩∘⟨ Equiv.sym F.homomorphism ⟩
               d C ∘ F.₁ (g.hom ∘ f.hom)   ∎
  ; comm-s = begin
               s A                 ≈⟨ f.comm-s ⟩
               s B ∘ f.hom         ≈⟨ pushˡ g.comm-s ⟩
               s C ∘ g.hom ∘ f.hom ∎
  } where module f = FMoore⇒ f
          module g = FMoore⇒ g

FMoore : Category (o ⊔ l) (o ⊔ l ⊔ e) e
FMoore = record
  { Obj = FMooreObj
  ; _⇒_ = FMoore⇒
  ; _≈_ = λ f g → hom f ≈ hom g
  ; id = λ { {A} → record
    { hom = id
    ; comm-d = begin
                 id ∘ d A ≈⟨ identityˡ ⟩
                 d A ≈˘⟨ MR.elimʳ C (Functor.identity F) ⟩
                 d A ∘ F.₁ id ∎
    ; comm-s = Equiv.sym identityʳ
    }}
  ; _∘_ = _⊚_
  ; assoc = assoc
  ; sym-assoc = sym-assoc
  ; identityˡ = identityˡ
  ; identityʳ = identityʳ
  ; identity² = identity²
  ; equiv = record { refl = Equiv.refl ; sym = Equiv.sym ; trans = Equiv.trans }
  ; ∘-resp-≈ = ∘-resp-≈
  } where open HomReasoning

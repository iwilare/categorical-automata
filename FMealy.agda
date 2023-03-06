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

module FMealy {o l e} {C : Category o l e} (F : Functor C C) (O : Category.Obj C) where

open Category C
open HomReasoning
open MR C

private
  module F = Functor F

record FMealyObj : Set (o ⊔ l) where
  field
    E : Obj
    d : F.F₀ E ⇒ E
    s : F.F₀ E ⇒ O

open FMealyObj public

record FMealy⇒ (A B : FMealyObj) : Set (o ⊔ l ⊔ e) where
  private
    module A = FMealyObj A
    module B = FMealyObj B
  field
    hom    : A.E ⇒ B.E
    comm-d : hom ∘ A.d ≈ B.d ∘ F.F₁ hom
    comm-s : A.s ≈ B.s ∘ F.F₁ hom

open FMealy⇒

_⊚_ : {A B C : FMealyObj} → FMealy⇒ B C → FMealy⇒ A B → FMealy⇒ A C
_⊚_ {A} {B} {C} g f = record
  { hom = hom g ∘ hom f
  ; comm-d = begin
               (g.hom ∘ f.hom) ∘ d A       ≈⟨ pullʳ f.comm-d ⟩
               g.hom ∘ d B ∘ F.₁ f.hom     ≈⟨ extendʳ g.comm-d ⟩
               d C ∘ F.₁ g.hom ∘ F.₁ f.hom ≈⟨ refl⟩∘⟨ Equiv.sym F.homomorphism ⟩
               d C ∘ F.₁ (g.hom ∘ f.hom)   ∎
  ; comm-s = begin
               s A                 ≈⟨ f.comm-s ⟩
               s B ∘ F.F₁ f.hom    ≈⟨ pushˡ g.comm-s ⟩
               s C ∘ F.F₁ g.hom ∘ F.F₁ f.hom ≈⟨ refl⟩∘⟨ Equiv.sym F.homomorphism ⟩
               s C ∘ F.F₁ (g.hom ∘ f.hom) ∎
  } where module f = FMealy⇒ f
          module g = FMealy⇒ g

FMealy : Category (o ⊔ l) (o ⊔ l ⊔ e) e
FMealy = record
  { Obj = FMealyObj
  ; _⇒_ = FMealy⇒
  ; _≈_ = λ f g → hom f ≈ hom g
  ; id = λ { {A} → record
    { hom = id
    ; comm-d = begin
                 id ∘ d A ≈⟨ identityˡ ⟩
                 d A ≈˘⟨ MR.elimʳ C (Functor.identity F) ⟩
                 d A ∘ F.₁ id ∎
    ; comm-s = introʳ F.identity
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

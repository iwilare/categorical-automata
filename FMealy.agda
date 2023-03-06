open import Level
open import Categories.Category
open import Categories.Functor renaming (id to idF)
import Categories.Morphism.Reasoning as MR

module FMealy {o l e} {C : Category o l e} {F : Functor C C} where

open Category C
open module F = Functor F

record FMealyObj {O : Obj} : Set (o ⊔ l) where
  field
    E : Obj
    d : F.F₀ E ⇒ E
    s : F.F₀ E ⇒ O

open FMealyObj

record FMealy⇒ {O : Obj} (A B : FMealyObj {O}) : Set (o ⊔ l ⊔ e) where
  private
    module A = FMealyObj A
    module B = FMealyObj B
  field
    hom    : A.E ⇒ B.E
    comm-d : hom ∘ A.d ≈ B.d ∘ F.F₁ hom
    comm-s : A.s ≈ B.s ∘ F.F₁ hom

open FMealy⇒

comp : {O : Obj} {A B C : FMealyObj {O}} → FMealy⇒ B C → FMealy⇒ A B → FMealy⇒ A C
comp g f = record
  { hom = hom g ∘ hom f
  ; comm-d = {!   !}
  ; comm-s = {!   !}
  }

FMCat : {O : Obj} → Category (o ⊔ l) (o ⊔ l ⊔ e) e
FMCat {O} = record
  { Obj = FMealyObj {O}
  ; _⇒_ = FMealy⇒ {O}
  ; _≈_ = λ f g → hom f ≈ hom g
  ; id = λ { {A} → record
    { hom = id
    ; comm-d = begin _ ≈⟨ identityˡ ⟩ _ ≈˘⟨ MR.elimʳ C (Functor.identity F) ⟩ _ ∎
    ; comm-s = Equiv.sym (MR.elimʳ C (Functor.identity F))
    }}
  ; _∘_ = comp
  ; assoc = {!   !}
  ; sym-assoc = {!   !}
  ; identityˡ = identityˡ
  ; identityʳ = identityʳ
  ; identity² = identity²
  ; equiv = record { refl = Equiv.refl ; sym = Equiv.sym ; trans = Equiv.trans }
  ; ∘-resp-≈ = ∘-resp-≈
  } where open HomReasoning

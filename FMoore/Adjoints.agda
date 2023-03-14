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

module FMoore.Adjoints {o l e} {C : Category o l e} {F : Functor C C} (O : Category.Obj C) where

open import Categories.Adjoint
open import FMoore F O
open Category C
open HomReasoning
open Equiv
pattern * = lift Data.Unit.tt

open F-Algebra

module _
   {R : Functor C C}
   (adj : F ⊣ R)
   {complete : ∀ {o ℓ e} → Complete o ℓ e C} where

  module adj = Adjoint adj

  open import FMoore.Limits F O adj complete

  open MR C

  o∞ : F-Algebra F
  o∞ = record
    { A = R∞.X
    ; α = d∞
    }

  B : Functor FMoore (Slice (F-Algebras F) o∞)
  B = record
    { F₀ = λ { A → sliceobj (record { f = behaviour A ; commutes = FMoore⇒.comm-d ⊤.! }) }
    ; F₁ = λ { M →
      let module M = FMoore⇒ M in
      slicearr {h = record { f = M.hom ; commutes = M.comm-d }}
               (Equiv.sym (commute-behaviour M)) }
    ; identity = Equiv.refl
    ; homomorphism = Equiv.refl
    ; F-resp-≈ = Fun.id
    }

  L : Functor (Slice (F-Algebras F) o∞) FMoore
  L = record
    { F₀ = λ { (sliceobj {record { A = A; α = α }} (record { f = f; commutes = commutes })) →
      record
        { E = A
        ; d = α
        ; s = R∞.π 0 ∘ f
        } }
    ; F₁ = λ slice@(slicearr {record { f = h; commutes = commutes }} f) →
      record
        { hom = h
        ; comm-d = commutes
        ; comm-s = pushʳ (Equiv.sym f)
        }
    ; identity = refl
    ; homomorphism = refl
    ; F-resp-≈ = λ F → F
    }

  L⊣B : L ⊣ B
  L⊣B = record
    { unit = ntHelper record
      { η = λ obj@(sliceobj {record { A = A; α = α }} arr@(record { f = f; commutes = commutes })) →
          slicearr {h = Category.id (F-Algebras F)}
           (begin behaviour (record { E = A ; d = α ; s = R∞.π 0 ∘ f }) ∘ id ≈⟨ identityʳ ⟩
                  behaviour (record { E = A ; d = α ; s = R∞.π 0 ∘ f })
                    ≈⟨ ⊤.!-unique (record
                       { hom = f
                       ; comm-d = commutes
                       ; comm-s = refl
                       }) ⟩
                  f ∎)
      ; commute = λ _ → id-comm-sym
      }
    ; counit = ntHelper record
       { η = λ A →
         let module A = FMooreObj A in
         record
           { hom = id
           ; comm-d = id-comm-sym ○ refl⟩∘⟨ Equiv.sym F.identity
           ; comm-s = ⟺ (FMoore⇒.comm-s ⊤.!) ○ Equiv.sym identityʳ
           }
       ; commute = λ _ → id-comm-sym
       }
    ; zig = identity²
    ; zag = identity²
    }

  module _ where

    forget : Functor (F-Algebras F) C
    forget = record
      { F₀ = F-Algebra.A
      ; F₁ = F-Algebra-Morphism.f
      ; identity = refl
      ; homomorphism = refl
      ; F-resp-≈ = λ F → F
      }

    module forget = Functor forget

    -- Requirement that F is an input process
    module _ (free : Functor C (F-Algebras F))
             (Free⊣Forget : free ⊣ forget) where

      module free = Functor free
      module Free⊣Forget = Adjoint Free⊣Forget

      open import Categories.Adjoint.Slice free forget Free⊣Forget o∞

      F~″ : Functor (Slice C (forget.₀ o∞)) (Slice (F-Algebras F) o∞)
      F~″ = G~

      U~″ : Functor (Slice (F-Algebras F) o∞) (Slice C (forget.₀ o∞))
      U~″ = U~

      F~′ : Functor (Slice C (forget.₀ o∞)) (Slice (F-Algebras F) o∞)
      F~′ = record
        { F₀ =
          λ { (sliceobj {Y} f) →
            sliceobj (record
              { f = behaviour (record
                { E = A (free.₀ Y)
                ; d = α (free.₀ Y)
                ; s = R∞.π 0 ∘ F-Algebra-Morphism.f (Free⊣Forget.counit.η o∞) ∘ F-Algebra-Morphism.f (free.₁ f)
                })
              ; commutes = FMoore⇒.comm-d ⊤.!
              }) }
        ; F₁ = λ { arr@(slicearr {h = h} c) →
            slicearr {h = free.₁ h}
              (begin
                  behaviour (record { E = A (free.₀ (SliceObj.Y (cod arr)))
                                     ; d = α (free.₀ (SliceObj.Y (cod arr)))
                                     ; s = _
                                     }) ∘ F-Algebra-Morphism.f (free.₁ h)
                        ≈⟨ Equiv.sym (commute-behaviour (record
                          { hom = F-Algebra-Morphism.f (free.₁ h)
                          ; comm-d = F-Algebra-Morphism.commutes (free.₁ h)
                          ; comm-s = pushʳ (pushʳ (free.F-resp-≈ (Equiv.sym c) ○ free.homomorphism))
                          })) ⟩
                  behaviour (record { E = A (free.₀ (SliceObj.Y (dom arr)))
                                     ; d = α (free.₀ (SliceObj.Y (dom arr)))
                                     ; s = _
                                     }) ∎) }
        ; identity = free.identity
        ; homomorphism = free.homomorphism
        ; F-resp-≈ = free.F-resp-≈
        }

      U~′ : Functor (Slice (F-Algebras F) o∞) (Slice C (forget.₀ o∞))
      U~′ = record
        { F₀ =
          λ (sliceobj {Y} (record { f = f ; commutes = commutes })) →
            sliceobj (behaviour (record { E = forget.₀ Y ; d = α Y ; s = R∞.π 0 ∘ f }))
        ; F₁ = λ (slicearr {h = h} c) →
            slicearr {h = forget.₁ h} (Equiv.sym (commute-behaviour (record
              { hom = forget.₁ h
              ; comm-d = F-Algebra-Morphism.commutes h
              ; comm-s = pushʳ (Equiv.sym c)
              })))
        ; identity = refl
        ; homomorphism = refl
        ; F-resp-≈ = λ F → F
        }

      open import Categories.Adjoint.Compose

      targetAdjunction : L ∘F G~ ⊣ U~ ∘F B
      targetAdjunction = G⊣U~ ∘⊣ L⊣B

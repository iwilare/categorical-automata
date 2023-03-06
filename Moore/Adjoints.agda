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

module Moore.Adjoints {o l e} {C : Category o l e} {X : Functor C C} (O : Category.Obj C) where

open import Categories.Adjoint
open import XMoore {o} {l} {e} {C} {X} O
open Category C
open HomReasoning
open Equiv
pattern * = lift Data.Unit.tt

{-
-- output functor
Bout : Functor XMoore (F ↘ O)
Bout = record
  { F₀ = λ { A → let module A = XMooreObj A in record { f = A.s ∘ A.d } }
  ; F₁ = λ { F → let module F = XMoore⇒ F in record
    { g = F.hom
    ; h = *
    ; commute = begin _ ≈⟨ identityˡ ○ F.comm-s ⟩∘⟨refl ⟩
                      _ ≈⟨ MR.pullʳ C F.comm-d ○ sym-assoc ⟩
                      _ ∎
    }}
  ; identity = refl , *
  ; homomorphism = refl , *
  ; F-resp-≈ = λ x → x , *
  }

-- in order to find a left adjoint to Bout we first have to define
-- an adjunction between Alg(F) and C: XMre has functors
-- Alg(F) <-pAlg- XMre -pSlice-> F/O
pAlg : Functor XMoore (F-Algebras F)
pAlg = record
  { F₀ = λ { A → let module A = XMooreObj A in record { A = A.E ; α = A.d }}
  ; F₁ = λ { F → let module F = XMoore⇒ F in record { f = F.hom ; commutes = F.comm-d }}
  ; identity = refl
  ; homomorphism = refl
  ; F-resp-≈ = λ x → x
  }

pSlice : Functor XMoore (Slice O)
pSlice = record
  { F₀ = λ { A → let module A = XMooreObj A in sliceobj A.s}
  ; F₁ = λ { F → let module F = XMoore⇒ F in slicearr {h = F.hom} (Equiv.sym F.comm-s) }
  ; identity = refl
  ; homomorphism = refl
  ; F-resp-≈ = λ x → x
  }
  -}

open F-Algebra

-- L : Functor (F ↘ O) XMoore
-- L = record
--   { F₀ = λ { record { α = Z ; β = β ; f = f } →
--       xobj (A (free.X₀ Z)) (α {F = F} (free.X₀ Z)) {!   !}}
--   ; F₁ = {!   !}
--   ; identity = {!   !}
--   ; homomorphism = {!   !}
--   ; F-resp-≈ = {!   !}
--   }

-- L⊣B : L ⊣ Bout
-- L⊣B = {!   !}


module _
   {R : Functor C C}
   (adj : X ⊣ R)
   {complete : ∀ {o ℓ e} → Complete o ℓ e C} where

  module adj = Adjoint adj
  open XMoore-Complete adj {complete = complete}

  open MR C

  o∞ : F-Algebra X
  o∞ = record
    { A = R∞.X
    ; α = d∞
    }

  B : Functor XMoore (Slice (F-Algebras X) o∞)
  B = record
    { F₀ = λ { A → sliceobj (record { f = behaviour A ; commutes = XMoore⇒.comm-d ⊤.! }) }
    ; F₁ = λ { F →
      let module F = XMoore⇒ F in
      slicearr {h = record { f = F.hom ; commutes = F.comm-d }}
               (Equiv.sym (commute-behaviour F)) }
    ; identity = Equiv.refl
    ; homomorphism = Equiv.refl
    ; F-resp-≈ = Fun.id
    }

  L : Functor (Slice (F-Algebras X) o∞) XMoore
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
    ; F-resp-≈ = λ x → x
    }

  L⊣B : L ⊣ B
  L⊣B = record
    { unit = ntHelper record
      { η = λ obj@(sliceobj {record { A = A; α = α }} arr@(record { f = f; commutes = commutes })) →
          slicearr {h = Category.id (F-Algebras X)}
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
         let module A = XMooreObj A in
         record
           { hom = id
           ; comm-d = id-comm-sym ○ refl⟩∘⟨ Equiv.sym X.identity
           ; comm-s = ⟺ (XMoore⇒.comm-s ⊤.!) ○ Equiv.sym identityʳ
           }
       ; commute = λ _ → id-comm-sym
       }
    ; zig = identity²
    ; zag = identity²
    }

  module _ where

    forget : Functor (F-Algebras X) C
    forget = record
      { F₀ = F-Algebra.A
      ; F₁ = F-Algebra-Morphism.f
      ; identity = refl
      ; homomorphism = refl
      ; F-resp-≈ = λ x → x
      }

    module forget = Functor forget

    -- Requirement that X is an input process
    module _ (free : Functor C (F-Algebras X))
             (Free⊣Forget : free ⊣ forget) where

      module free = Functor free
      module Free⊣Forget = Adjoint Free⊣Forget

      open import Categories.Adjoint.Slice free forget Free⊣Forget o∞

      F~″ : Functor (Slice C (forget.₀ o∞)) (Slice (F-Algebras X) o∞)
      F~″ = G~

      F~′ : Functor (Slice C (forget.₀ o∞)) (Slice (F-Algebras X) o∞)
      F~′ = record
        { F₀ =
          λ { (sliceobj {Y} f) →
            sliceobj (record
              { f = behaviour (record
                { E = A (free.₀ Y)
                ; d = α (free.₀ Y)
                ; s = R∞.π 0 ∘ F-Algebra-Morphism.f (Free⊣Forget.counit.η o∞) ∘ F-Algebra-Morphism.f (free.₁ f)
                })
              ; commutes = XMoore⇒.comm-d ⊤.!
              }) }
        ; F₁ = λ { arr@(slicearr {h = h} c) →
            slicearr {h = free.₁ h}
              (begin
                  behaviour (record { E = A (free.₀ (SliceObj.Y (Slice⇒.cod arr)))
                                     ; d = α (free.₀ (SliceObj.Y (Slice⇒.cod arr)))
                                     ; s = _
                                     }) ∘ F-Algebra-Morphism.f (free.₁ h)
                        ≈⟨ Equiv.sym (commute-behaviour (record
                          { hom = F-Algebra-Morphism.f (free.₁ h)
                          ; comm-d = F-Algebra-Morphism.commutes (free.₁ h)
                          ; comm-s = pushʳ (pushʳ (free.F-resp-≈ (Equiv.sym c) ○ free.homomorphism))
                          })) ⟩
                  behaviour (record { E = A (free.₀ (SliceObj.Y (Slice⇒.dom arr)))
                                     ; d = α (free.₀ (SliceObj.Y (Slice⇒.dom arr)))
                                     ; s = _
                                     }) ∎) }
        ; identity = free.identity
        ; homomorphism = free.homomorphism
        ; F-resp-≈ = free.F-resp-≈
        }

      U~′ : Functor (Slice (F-Algebras X) o∞) (Slice C (forget.₀ o∞))
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
        ; F-resp-≈ = λ x → x
        }

      open import Categories.Category.Instance.Cats using (Cats)

      module _ where
        module Cats = Category (Cats {!   !} {!   !} {!   !}) -- (Functors (Slice C (forget.₀ o∞)) (Slice (F-Algebras X) o∞))

        t : F~″ Cats.≈ F~′
        t = record { F⇒G = record { η = λ X → slicearr {h = {! free.F₁ (SliceObj.arr X)  !}} {!   !} ; commute = {!   !} ; sym-commute = {!   !} }
                   ; F⇐G = record { η = λ X → slicearr {h = {! free.F₁ (SliceObj.arr X)  !}} {!   !} ; commute = {! λ x → refl  !} ; sym-commute = {!   !} }
                   ; iso = λ X₂ → {!   !} }


{-

      F~⊣U~ : F~ ⊣ U~
      F~⊣U~ = record
        { unit = ntHelper record
          { η = λ { (sliceobj {Y} arr) →
              slicearr {h = Free⊣Forget.unit.η Y}
                (begin
                  behaviour (record { E = A (free.F₀ Y)
                                    ; d = α (free.F₀ Y)
                                    ; s = R∞.π 0
                                        ∘ F-Algebra-Morphism.f (SliceObj.arr (₀ F~ (sliceobj arr))) --(SliceObj.arr (₀ F~ (sliceobj arr)))
                                    })
                    ∘ Free⊣Forget.unit.η Y
                    ≈⟨ Equiv.sym (commute-behaviour (record
                      { hom = _
                      ; comm-d = Free⊣Forget.unit.commute _ ○ {!  F-Algebra-Morphism.commutes (free.₁ ?)  !} ○ {!   !} ○ {!   !} --F-Algebra-Morphism.commutes (free.₁ arr)  !} --Free⊣Forget.unit.commute _ ○ {!   !}
                      ; comm-s = {!   !} })) ⟩  --Equiv.sym (⊤.!-unique {A = record { E = Y ; d = {! α (free.₀ Y)  !} ; s = R∞.π 0 ∘ arr }} (record
                          --  { hom = _
                          --  ; comm-d =
                          --     begin (behaviour _ ∘ Free⊣Forget.unit.η Y) ∘ {!   !} ≈⟨ assoc ⟩
                          --           behaviour _ ∘ Free⊣Forget.unit.η Y ∘ {!   !} ≈⟨ {!  !} ⟩
                          --           d∞ ∘ X.₁ (behaviour _) ∘  X.₁ (Free⊣Forget.unit.η Y) ≈⟨ refl⟩∘⟨ Equiv.sym X.homomorphism ⟩
                          --           d∞ ∘ X.₁ (behaviour _ ∘ Free⊣Forget.unit.η Y) ∎
                          --  ; comm-s = begin {!   !} ≈⟨ refl⟩∘⟨ {!   !} ⟩ {!   !} ≈⟨ Equiv.sym {! ⊤.!-unique ?  !} ⟩ {!   !} ∎
                          --  })) ⟩
                  behaviour (record { E = Y ; d = _ ; s = R∞.π 0 ∘ arr })
                     ≈⟨ ⊤.!-unique (record { hom = arr ; comm-d = {! F-Algebra-Morphism.commutes (free.₁ arr)  !} ; comm-s = refl }) ⟩
                  arr ∎) }
          ; commute = λ (slicearr {h = h} c) → Free⊣Forget.unit.commute h
          }
        ; counit = ntHelper record
          { η = λ { (sliceobj {Y} alg) →
              slicearr {h = Free⊣Forget.counit.η Y}
                (begin
                  F-Algebra-Morphism.f alg ∘ F-Algebra-Morphism.f (Free⊣Forget.counit.η Y)
                    ≈⟨ Equiv.sym (Free⊣Forget.counit.commute alg) ⟩
                  F-Algebra-Morphism.f (Free⊣Forget.counit.η o∞) ∘ F-Algebra-Morphism.f (free.F₁ (F-Algebra-Morphism.f alg))
                    ≈⟨ Equiv.sym (⊤.!-unique (record
                       { hom = _
                       ; comm-d =
                          begin  (F-Algebra-Morphism.f (Free⊣Forget.counit.η o∞)
                                 ∘ F-Algebra-Morphism.f (free.F₁ (F-Algebra-Morphism.f alg)))
                                 ∘ α (free.F₀ (A Y)) ≈⟨ assoc ⟩
                                 {!   !} ≈⟨ {! XMoore⇒.comm-d ⊤.! !} ⟩
                                 {!   !} ≈⟨ {!  Free⊣Forget.counit.commute !} ⟩
                                 {!   !} ≈⟨ {! XMoore⇒.comm-d ⊤.!  !} ⟩
                                 d∞ ∘ X.₁ {!   !}
                                    ∘ X.₁ (F-Algebra-Morphism.f (free.F₁ (F-Algebra-Morphism.f alg))) ≈⟨ refl⟩∘⟨ X.F-resp-≈ (⊤.!-unique
                                      (record { hom = _ ; comm-d = {!   !} ; comm-s = {!   !} })) ⟩∘⟨refl ⟩
                                 d∞ ∘ X.₁ (F-Algebra-Morphism.f (Free⊣Forget.counit.η o∞))
                                    ∘ X.₁ (F-Algebra-Morphism.f (free.F₁ (F-Algebra-Morphism.f alg))) ≈⟨ refl⟩∘⟨ Equiv.sym X.homomorphism ⟩
                                 d∞ ∘ X.₁ ((F-Algebra-Morphism.f (Free⊣Forget.counit.η o∞)
                                 ∘ F-Algebra-Morphism.f (free.F₁ (F-Algebra-Morphism.f alg)))) ∎
                       ; comm-s = refl⟩∘⟨ refl⟩∘⟨ free.F-resp-≈ (⊤.!-unique (record { hom = _ ; comm-d = F-Algebra-Morphism.commutes alg ; comm-s = refl })) })) ⟩
                  behaviour (record { E = A (F₀ (free ∘F forget) Y)
                                    ; d = α (F₀ (free ∘F forget) Y)
                                    ; s = _ }) ∎) }
          ; commute = λ (slicearr {h = h} c) → Free⊣Forget.counit.commute h
          }
        ; zig = Free⊣Forget.zig
        ; zag = Free⊣Forget.zag
        }
        -}
{-
  L : Functor (Slice (forget.₀ o∞)) XMoore
  L = record
    { F₀ = λ { (sliceobj {A} arr)  → record
      { E = forget.₀ (free.₀ A)
      ; d = F-Algebra.α (free.₀ A)
      ; s = R∞.π 0 ∘ F-Algebra-Morphism.f (Free⊣Forget.Radjunct {A = A} {B = o∞} arr)
      } }
    ; F₁ = λ { Test@(slicearr {arr} △) → record
      { hom = F-Algebra-Morphism.f (free.₁ arr)
      ; comm-d = F-Algebra-Morphism.commutes (free.₁ arr)
      ; comm-s =
      begin
        R∞.π 0 ∘ F-Algebra-Morphism.f _ --((F-Algebras F) [ {! Category.id (F-Algebras F)  !} ∘ {!   !} ])
          ≈⟨ refl⟩∘⟨ pushˡ (Equiv.sym identityˡ) ⟩
        R∞.π 0 ∘ F-Algebra-Morphism.f _ --((F-Algebras F) [ Free⊣Forget.Radjunct {!  F-Algebra.α (free.₀ _) !} ∘ free.₁ arr ])
          ≈⟨ refl⟩∘⟨ Equiv.sym (Adjoint.Radjunct-square Free⊣Forget _ _ _ (Category.id (F-Algebras F)) (△ ○ Equiv.sym identityˡ)) ⟩
        R∞.π 0 ∘ F-Algebra-Morphism.f _ ∘ F-Algebra-Morphism.f (free.₁ arr)
          ≈⟨ sym-assoc ⟩
        (R∞.π 0 ∘ F-Algebra-Morphism.f _ {-(Adjoint.Radjunct Free⊣Forget ?)-}) ∘ F-Algebra-Morphism.f (free.₁ arr) ∎
      } }
    ; identity     = free.identity
    ; homomorphism = free.homomorphism
    ; F-resp-≈     = free.F-resp-≈
    }
  module L = Functor L
  -}
{-
  module _ (A : SliceObj R∞.X) where
    private module A = SliceObj A

    mister : behaviour (L.₀ A) ≈ F-Algebra-Morphism.f (Adjoint.Radjunct Free⊣Forget A.arr)
    mister = begin
      behaviour (₀ L A)
        ≈⟨ {!   !} ⟩
      {!   !}
        ≈⟨ {!   !} ⟩
      F-Algebra-Morphism.f (Adjoint.Radjunct Free⊣Forget A.arr)
        ∎

  -- the following is a proof that slaicia is a left adjoint to B
  -- (which is a right adjoint to R)
  -- the proof is a bit long, but it is not too complicated
  adj-slaicia : L ⊣ slaicia
  adj-slaicia = record
    { unit = ntHelper record
      { η = λ A →
       let module A = SliceObj A in
              slicearr {_} {h = Free⊣Forget.unit.η A.Y}
                ({!   !} ⟩∘⟨refl ○ Free⊣Forget.LRadjunct≈id {f = A.arr})
              --({!   !} ○ Free⊣Forget.LRadjunct≈id {f = A.arr})
              --(begin
              --  {!  d∞ ∘ ? !} ≈⟨ {!   !} ⟩
              --  {!   !} ∎)
      ; commute = {!   !}
      }
    ; counit = {!   !}
    ; zig = {!   !}
    ; zag = {!   !}
    }
-}
{-

d∞


Categories.Diagram.Cone.Cone⇒.arr
(IsTerminal.!
 (Terminal.⊤-is-terminal
  (Categories.Diagram.Limit.Limit.terminal
   (complete
    (Categories.Category.Construction.StrictDiscrete.lift-func C
     (R ^_$ O)
     ∘F
     Categories.Category.Lift.unliftF Level.zero Level.zero Level.zero
     (Categories.Category.Construction.StrictDiscrete.Discrete ℕ))))))
-}

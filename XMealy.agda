open import Level
open import Categories.Category
open import Categories.Functor renaming (id to idF)
import Categories.Morphism.Reasoning as MR

module XMealy {o l e} {C : Category o l e} {X : Functor C C} where

open Category C
open module X = Functor X

record XMealyObj {O : Obj} : Set (o ⊔ l) where
  field
    E : Obj
    d : X.F₀ E ⇒ E
    s : X.F₀ E ⇒ O

open XMealyObj

record XMealy⇒ {O : Obj} (A B : XMealyObj {O}) : Set (o ⊔ l ⊔ e) where
  private
    module A = XMealyObj A
    module B = XMealyObj B
  field
    hom    : A.E ⇒ B.E
    comm-d : hom ∘ A.d ≈ B.d ∘ X.F₁ hom
    comm-s : A.s ≈ B.s ∘ X.F₁ hom

open XMealy⇒

comp : {O : Obj} {A B C : XMealyObj {O}} → XMealy⇒ B C → XMealy⇒ A B → XMealy⇒ A C
comp g f = record
  { hom = hom g ∘ hom f
  ; comm-d = {!   !}
  ; comm-s = {!   !}
  }

XMCat : {O : Obj} → Category (o ⊔ l) (o ⊔ l ⊔ e) e
XMCat {O} = record
  { Obj = XMealyObj {O}
  ; _⇒_ = XMealy⇒ {O}
  ; _≈_ = λ f g → hom f ≈ hom g
  ; id = λ { {A} → record
    { hom = id
    ; comm-d = begin _ ≈⟨ identityˡ ⟩ _ ≈˘⟨ MR.elimʳ C (Functor.identity X) ⟩ _ ∎
    ; comm-s = Equiv.sym (MR.elimʳ C (Functor.identity X))
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


-- if X is left adjoint, and C has pullbacks, then XMach has products (and then equalizers)

open import Categories.Category.Complete.Finitely using (FinitelyComplete)
open import Categories.Category.Cartesian using (Cartesian)
open import Categories.Diagram.Pullback using (Pullback)
open import Categories.Category.BinaryProducts using (BinaryProducts)

  -- open import Categories.Adjoint
  -- open import Categories.Category.BinaryProducts (Cartesian.products cartesian)
  -- -- open import Categories.Diagram.Pullback
  -- open import Categories.Object.Product

  -- open Product

  -- module R = Functor R

  -- thmmmh : {O : Obj} → (adj : X ⊣ R) → BinaryProducts (XMCat {O})
  -- thmmmh adj = record
  --   { product = λ { {A} {B} → let module A = XMealyObj A in
  --     let module B = XMealyObj B in
  --       record
  --       { A×B = let P = pullback (Ladjunct A.s) (Ladjunct B.s) in let module P = Pullback P in record
  --         { E = P.P
  --         ; d = P.universal {X.F₀ P.P} {A.d ∘ X.F₁ P.p₁} {B.d ∘ X.F₁ P.p₂}
  --           (begin {!   !} ≈⟨ assoc ⟩
  --                 {!   !} ≈⟨ (refl⟩∘⟨ MR.extendʳ C (unit.commute _)) ⟩
  --                 {!   !} ≈⟨ (refl⟩∘⟨ (refl⟩∘⟨ unit.commute _)) ⟩
  --                 {!   !} ≈⟨ {!   !} ⟩
  --                 {!   !} ≈⟨ {!   !} ⟩
  --                 {!   !} ≈⟨ {!   !} ⟩
  --                 {!   !} ≈⟨ {!   !} ⟩
  --                 {!   !} ∎)
  --         -- XP --> XRO --> O
  --         ; s = Radjunct P.diag
  --         }
  --       ; π₁ = {!   !}
  --       ; π₂ = {!   !}
  --       ; ⟨_,_⟩ = {!   !}
  --       ; project₁ = {!   !}
  --       ; project₂ = {!   !}
  --       ; unique = {!   !}
  --       }}
  --   } where open Adjoint adj
  --           open HomReasoning
module _ {R : Functor C C} {hasFL : FinitelyComplete C} where

  open FinitelyComplete hasFL
  open BinaryProducts (Cartesian.products cartesian)
  -- open Cartesian cartesian using (products)

  open import Categories.Adjoint
  -- open import Categories.Category.BinaryProducts (Cartesian.products cartesian)
  -- -- open import Categories.Diagram.Pullback
  -- open import Categories.Object.Product

  -- open Product

  module R = Functor R

  thmmmh : {O : Obj} → (adj : X ⊣ R) → BinaryProducts (XMCat {O})
  thmmmh adj = record
    { product = λ { {A} {B} → let module A = XMealyObj A in
      let module B = XMealyObj B in
        record
        { A×B = let P = pullback (Ladjunct A.s) (Ladjunct B.s) in let module P = Pullback P in record
          { E = P.P
          ; d = P.universal {X.F₀ P.P} {A.d ∘ X.F₁ P.p₁} {B.d ∘ X.F₁ P.p₂}
            (begin {!   !} ≈⟨ assoc ⟩
                  {!   !} ≈⟨ (refl⟩∘⟨ MR.extendʳ C (unit.commute _)) ⟩
                  {!   !} ≈⟨ (refl⟩∘⟨ (refl⟩∘⟨ unit.commute _)) ⟩
                  {!   !} ≈⟨ {!   !} ⟩
                  {!   !} ≈⟨ {!   !} ⟩
                  {!   !} ≈⟨ {!   !} ⟩
                  {!   !} ≈⟨ {!   !} ⟩
                  {!   !} ∎)
          -- XP --> XRO --> O
          ; s = Radjunct P.diag
          }
        ; π₁ = {!   !}
        ; π₂ = {!   !}
        ; ⟨_,_⟩ = {!   !}
        ; project₁ = {!   !}
        ; project₂ = {!   !}
        ; unique = {!   !}
        }}
    } where open Adjoint adj
            open HomReasoning

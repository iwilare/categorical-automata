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

-- if F is left adjoint, and C has pullbacks, then FMach has products (and then equalizers)
module FMoore.Limits {o l e} {C : Category o l e} {F : Functor C C} (O : Category.Obj C)
                     {R : Functor C C} (adj : F ⊣ R) {complete : ∀ {o ℓ e} → Complete o ℓ e C}where

  open import FMoore O

  open Category C
  open HomReasoning
  open MR C
  module F = Functor F

  open import Categories.Object.Product.Indexed.Properties C
  open import Categories.Diagram.Pullback.Limit C

  module R = Functor R

  open Adjoint adj

  _^_$_ : Functor C C → ℕ → Obj → Obj
  F ^ zero  $ O = O
  F ^ suc n $ O = Functor.₀ F (F ^ n $ O)

  R∞ : IndexedProductOf C (R ^_$ O)
  R∞ = Complete⇒IndexedProductOf {0ℓ} {0ℓ} {0ℓ} {0ℓ} complete {I = ℕ} (R ^_$ O)

  Rδ : (A : FMooreObj) (i : ℕ) → E A ⇒ R ^ i $ O
  Rδ A zero = s A
  Rδ A (suc i) = Ladjunct (Rδ A i ∘ d A)

  module R∞ = IndexedProductOf R∞

  behaviour : (A : FMooreObj) → E A ⇒ R∞.X
  behaviour A = R∞.⟨ Rδ A ⟩

  d∞ : F.₀ R∞.X ⇒ R∞.X
  d∞ = R∞.⟨ (λ i → Radjunct (R∞.π (ℕ.suc i))) ⟩

  Terminal-FMoore : Terminal FMoore
  Terminal-FMoore = record
    { ⊤ = record
      { E = R∞.X
      ; d = d∞
      ; s = R∞.π 0
      }
    ; ⊤-is-terminal = record
      { ! = λ {A} → let module A = FMooreObj A in record
        { hom = behaviour A
        ; comm-d =
            begin
              R∞.⟨ Rδ A ⟩ ∘ A.d
                ≈⟨ R∞.⟨⟩∘ (Rδ A) (d A) ⟩
              R∞.⟨ (λ i → Rδ A i ∘ A.d) ⟩
                ≈⟨ R∞.⟨⟩-cong _ _ pointwise-comm-d ⟩
              R∞.⟨ (λ i → (Radjunct (R∞.π (ℕ.suc i))) ∘ F.₁ (behaviour A)) ⟩
                ≈⟨ ⟺ (R∞.⟨⟩∘ _ (F.₁ (behaviour A))) ⟩
              d∞ ∘ F.₁ (behaviour A) ∎
        ; comm-s = ⟺ (R∞.commute (Rδ A) 0)
        }
      ; !-unique = λ {A} f → R∞.unique _ _ (uniqueness f)
      }
    } where

      module _ {A : FMooreObj} where
        private module A = FMooreObj A

        module _ (f : FMoore⇒ A _) where
          private module f = FMoore⇒ f
          uniqueness : (i : ℕ) → R∞.π i ∘ f.hom ≈ Rδ A i
          uniqueness ℕ.zero = Equiv.sym f.comm-s
          uniqueness (ℕ.suc i) = begin
            R∞.π (ℕ.suc i) ∘ f.hom
              ≈⟨ introˡ zag ⟩
            (R.₁ (counit.η (R ^ i $ O)) ∘ unit.η _) ∘ R∞.π (ℕ.suc i) ∘ f.hom
              ≈⟨ assoc ⟩
            R.₁ (counit.η (R ^ i $ O)) ∘ unit.η _ ∘ R∞.π (ℕ.suc i) ∘ f.hom
              ≈⟨ refl⟩∘⟨ unit.commute _ ⟩
            R.₁ (counit.η (R ^ i $ O)) ∘ R.₁ (F.₁ (R∞.π (ℕ.suc i) ∘ f.hom)) ∘ unit.η _
              ≈⟨ pullˡ (Equiv.sym R.homomorphism) ⟩
            R.₁ (counit.η (R ^ i $ O) ∘ F.₁ (R∞.π (ℕ.suc i) ∘ f.hom)) ∘ unit.η _
              ≈⟨ R.F-resp-≈ (refl⟩∘⟨ F.homomorphism) ⟩∘⟨refl ⟩
            R.₁ (counit.η (R ^ i $ O) ∘ F.₁ (R∞.π (ℕ.suc i)) ∘ F.₁ f.hom) ∘ unit.η _
              ≈⟨ R.F-resp-≈ (extendʳ (Equiv.sym (R∞.commute _ i))) ⟩∘⟨refl ⟩
            R.₁ (R∞.π i ∘ d∞ ∘ F.₁ f.hom) ∘ unit.η _
              ≈⟨ R.F-resp-≈ (refl⟩∘⟨ Equiv.sym f.comm-d) ⟩∘⟨refl ⟩
            R.₁ (R∞.π i ∘ f.hom ∘ A.d) ∘ unit.η _
              ≈⟨ R.F-resp-≈ (pullˡ (uniqueness i)) ⟩∘⟨refl ⟩
            R.₁ (Rδ A i ∘ A.d) ∘ unit.η _
              ≈⟨ Equiv.refl ⟩
            Ladjunct (Rδ A i ∘ A.d) ∎

        abstract
          pointwise-comm-d : (i : ℕ)
            → Rδ A i ∘ A.d
            ≈ Radjunct (R∞.π (ℕ.suc i)) ∘ F.₁ (behaviour A)
          pointwise-comm-d i = begin
            Rδ A i ∘ A.d ≈⟨ Equiv.sym (elimʳ zig) ⟩
            (Rδ A i ∘ A.d) ∘ counit.η (F.F₀ A.E) ∘ F.₁ (unit.η A.E) ≈⟨ Equiv.sym (extendʳ (counit.commute _)) ⟩
            counit.η (R ^ i $ O) ∘ F.₁ (R.₁ (Rδ A i ∘ A.d)) ∘ F.₁ (unit.η A.E) ≈⟨ refl⟩∘⟨ Equiv.sym F.homomorphism ⟩
            counit.η (R ^ i $ O) ∘ F.₁ (Ladjunct (Rδ A i ∘ A.d)) ≈⟨ refl⟩∘⟨ F.F-resp-≈ (Equiv.sym (R∞.commute _ (ℕ.suc i))) ⟩
            counit.η (R ^ i $ O) ∘ F.₁ (R∞.π (ℕ.suc i) ∘ R∞.⟨ Rδ A ⟩) ≈⟨ refl⟩∘⟨ F.homomorphism ⟩
            counit.η (R ^ i $ O) ∘ F.₁ (R∞.π (ℕ.suc i)) ∘ F.₁ R∞.⟨ Rδ A ⟩ ≈⟨ sym-assoc ⟩
            Radjunct (R∞.π (ℕ.suc i)) ∘ F.₁ R∞.⟨ Rδ A ⟩ ∎

  module ⊤ = Terminal Terminal-FMoore
  module _ {A B : FMooreObj} where
    private
      module A = FMooreObj A
      module B = FMooreObj B
      module P = Pullback (complete⇒pullback complete (behaviour A) (behaviour B))

    module P∞ = Pullback (complete⇒pullback complete (behaviour A) (behaviour B))

    abstract
      universal-d : behaviour A ∘ A.d ∘ F.F₁ P∞.p₁
                  ≈ behaviour B ∘ B.d ∘ F.F₁ P∞.p₂
      universal-d = begin
        behaviour A ∘ A.d ∘ F.F₁ P∞.p₁      ≈⟨ extendʳ (comm-d (⊤.! {A})) ⟩
        _ ∘ F.F₁ (behaviour A) ∘ F.F₁ P∞.p₁ ≈⟨ refl⟩∘⟨ (Equiv.sym F.homomorphism ○ F.F-resp-≈ P∞.commute ○ F.homomorphism) ⟩
        _ ∘ F.₁ (behaviour B) ∘ F.F₁ P∞.p₂  ≈⟨ extendʳ (Equiv.sym (comm-d (⊤.! {B}))) ⟩
        behaviour B ∘ B.d ∘ F.F₁ P∞.p₂ ∎

    module _ {G : FMooreObj} (PA : FMoore⇒ G A) (PB : FMoore⇒ G B) where
      private
        module G  = FMooreObj G
        module PA = FMoore⇒ PA
        module PB = FMoore⇒ PB

      abstract
        universal-⟨-,-⟩ : R∞.⟨ Rδ A ⟩ ∘ PA.hom ≈ R∞.⟨ Rδ B ⟩ ∘ PB.hom
        universal-⟨-,-⟩ = begin
          R∞.⟨ Rδ A ⟩ ∘ PA.hom           ≈⟨ R∞.⟨⟩∘ _ _ ⟩
          R∞.⟨ (λ i → Rδ A i ∘ PA.hom) ⟩ ≈⟨ R∞.⟨⟩-cong _ _ universal-⟨-,-⟩-pointwise ⟩
          R∞.⟨ (λ i → Rδ B i ∘ PB.hom) ⟩ ≈˘⟨ R∞.⟨⟩∘ _ _ ⟩
          R∞.⟨ Rδ B ⟩ ∘ PB.hom ∎
          where
            universal-⟨-,-⟩-pointwise : (i : ℕ)
                      → Rδ A i ∘ PA.hom ≈ Rδ B i ∘ PB.hom
            universal-⟨-,-⟩-pointwise ℕ.zero = Equiv.sym PA.comm-s ○ PB.comm-s
            universal-⟨-,-⟩-pointwise (ℕ.suc i) = begin
              (R.F₁ (Rδ A i ∘ A.d) ∘ unit.η A.E) ∘ PA.hom
                ≈⟨ pullʳ (unit.commute _) ⟩
              R.F₁ (Rδ A i ∘ A.d) ∘ R.F₁ (F.₁ PA.hom) ∘ unit.η G.E
                ≈⟨ pullˡ (Equiv.sym R.homomorphism) ⟩
              R.F₁ ((Rδ A i ∘ A.d) ∘ F.₁ PA.hom) ∘ unit.η G.E
                ≈⟨ R.F-resp-≈ (pullʳ (Equiv.sym PA.comm-d)) ⟩∘⟨refl ⟩
              R.F₁ (Rδ A i ∘ PA.hom ∘ d G) ∘ unit.η G.E
                ≈⟨ R.F-resp-≈ (extendʳ (universal-⟨-,-⟩-pointwise i)) ⟩∘⟨refl ⟩
              R.F₁ (Rδ B i ∘ PB.hom ∘ d G) ∘ unit.η G.E
                ≈˘⟨ R.F-resp-≈ (pullʳ (Equiv.sym PB.comm-d)) ⟩∘⟨refl ⟩
              R.F₁ ((Rδ B i ∘ B.d) ∘ F.₁ PB.hom) ∘ unit.η G.E
                ≈˘⟨ pullˡ (Equiv.sym R.homomorphism) ⟩
              R.F₁ (Rδ B i ∘ B.d) ∘ R.₁ (F.₁ PB.hom) ∘ unit.η G.E
                ≈˘⟨ pullʳ (unit.commute _) ⟩
              (R.F₁ (Rδ B i ∘ B.d) ∘ unit.η B.E) ∘ PB.hom ∎

  module _ {A G : FMooreObj} (PA :  FMoore⇒ G A) where
    private
      module G  = FMooreObj G
      module A  = FMooreObj A
      module PA = FMoore⇒ PA

    abstract
      commute-behaviour : behaviour G ≈ behaviour A ∘ PA.hom
      commute-behaviour =
        begin
          behaviour G                    ≈⟨ R∞.⟨⟩-cong _ _ commute-behaviour-pointwise ⟩
          R∞.⟨ (λ i → Rδ A i ∘ PA.hom) ⟩ ≈⟨ Equiv.sym (R∞.⟨⟩∘ _ _) ⟩
          behaviour A ∘ PA.hom           ∎
        where
          commute-behaviour-pointwise : (i : ℕ) → Rδ G i ≈ Rδ A i ∘ PA.hom
          commute-behaviour-pointwise ℕ.zero = PA.comm-s
          commute-behaviour-pointwise (ℕ.suc i) = begin
            R.F₁ (Rδ G i ∘ d G) ∘ unit.η G.E                     ≈⟨ R.F-resp-≈ (pushˡ (commute-behaviour-pointwise i)) ⟩∘⟨refl ⟩
            R.F₁ (Rδ A i ∘ PA.hom ∘ d G) ∘ unit.η G.E            ≈⟨ R.F-resp-≈ (refl⟩∘⟨ PA.comm-d) ⟩∘⟨refl ⟩
            R.F₁ (Rδ A i ∘ A.d ∘ F.₁ PA.hom) ∘ unit.η G.E        ≈⟨ R.F-resp-≈ sym-assoc ⟩∘⟨refl ⟩
            R.F₁ ((Rδ A i ∘ A.d) ∘ F.₁ PA.hom) ∘ unit.η G.E      ≈⟨ pushˡ R.homomorphism ⟩
            R.F₁ (Rδ A i ∘ A.d) ∘ R.F₁ (F.₁ PA.hom) ∘ unit.η G.E ≈⟨ refl⟩∘⟨ unit.sym-commute _ ⟩
            R.F₁ (Rδ A i ∘ A.d) ∘ unit.η A.E ∘ PA.hom            ≈⟨ sym-assoc ⟩
            Ladjunct (Rδ A i ∘ A.d) ∘ PA.hom                     ∎

  BinaryProducts-FMoore : BinaryProducts FMoore
  BinaryProducts-FMoore = record
    { product = λ { {A} {B} →
    let module A = FMooreObj A
        module B = FMooreObj B in
      record
        { A×B = record
          { E = P∞.P
          ; d = P∞.universal {_} {_} {F.F₀ P∞.P} {A.d ∘ F.₁ P∞.p₁} {B.d ∘ F.₁ P∞.p₂} universal-d
          ; s = R∞.π 0 ∘ P∞.diag
          }
        ; π₁ = record
          { hom = P∞.p₁
          ; comm-d = P∞.p₁∘universal≈h₁
          ; comm-s = begin
               R∞.π 0 ∘ behaviour A ∘ P∞.p₁ ≈⟨ pullˡ (Equiv.sym (comm-s (⊤.! {A}))) ⟩
               A.s ∘ P∞.p₁                  ∎
          }
        ; π₂ = record
          { hom = P∞.p₂
          ; comm-d = P∞.p₂∘universal≈h₂
          ; comm-s = begin
               R∞.π 0 ∘ behaviour A ∘ P∞.p₁ ≈⟨ refl⟩∘⟨ P∞.commute ⟩
               R∞.π 0 ∘ behaviour B ∘ P∞.p₂ ≈⟨ pullˡ (Equiv.sym (comm-s (⊤.! {B}))) ⟩
               B.s ∘ P∞.p₂ ∎
          }
        ; ⟨_,_⟩ =
            λ {C} PA PB →
            let module PA = FMoore⇒ PA
                module PB = FMoore⇒ PB
                in record
            { hom = P∞.universal {_} {_} {E C} {PA.hom} {PB.hom} (universal-⟨-,-⟩ PA PB)
            ; comm-d = P∞.unique-diagram
                         (begin P∞.p₁ ∘ P∞.universal (universal-⟨-,-⟩ PA PB) ∘ d C                             ≈⟨ pullˡ (P∞.p₁∘universal≈h₁ {h₁ = PA.hom} {_} {eq = (universal-⟨-,-⟩ PA PB)}) ⟩
                                PA.hom ∘ d C                                                                   ≈⟨ PA.comm-d ⟩
                                A.d ∘ F.F₁ PA.hom                                                              ≈⟨ refl⟩∘⟨ F.F-resp-≈ (Equiv.sym P∞.p₁∘universal≈h₁)  ⟩
                                A.d ∘ F.F₁ (P∞.p₁ ∘ P∞.universal (universal-⟨-,-⟩ PA PB))                      ≈⟨ refl⟩∘⟨ F.homomorphism ⟩
                                A.d ∘ F.F₁ P∞.p₁ ∘ F.F₁ (P∞.universal (universal-⟨-,-⟩ PA PB))                 ≈⟨ extendʳ (Equiv.sym P∞.p₁∘universal≈h₁ ) ⟩
                                P∞.p₁ ∘ P∞.universal universal-d ∘ F.F₁ (P∞.universal (universal-⟨-,-⟩ PA PB)) ∎)
                         (begin P∞.p₂ ∘ P∞.universal (universal-⟨-,-⟩ PA PB) ∘ d C                             ≈⟨ pullˡ (P∞.p₂∘universal≈h₂ ) ⟩
                                PB.hom ∘ d C                                                                   ≈⟨ PB.comm-d ⟩
                                B.d ∘ F.F₁ PB.hom                                                              ≈⟨ refl⟩∘⟨ F.F-resp-≈ (Equiv.sym P∞.p₂∘universal≈h₂) ⟩
                                B.d ∘ F.F₁ (P∞.p₂ ∘ P∞.universal (universal-⟨-,-⟩ PA PB))                      ≈⟨ refl⟩∘⟨ F.homomorphism ⟩
                                B.d ∘ F.F₁ P∞.p₂ ∘ F.F₁ (P∞.universal (universal-⟨-,-⟩ PA PB))                 ≈⟨ extendʳ (Equiv.sym P∞.p₂∘universal≈h₂ ) ⟩
                                P∞.p₂ ∘ P∞.universal universal-d ∘ F.F₁ (P∞.universal (universal-⟨-,-⟩ PA PB)) ∎)
            ; comm-s = begin
                s C                                 ≈⟨ comm-s (⊤.! {C}) ⟩
                R∞.π 0 ∘ behaviour C                ≈⟨ refl⟩∘⟨
                commute-behaviour PA ⟩
                R∞.π 0 ∘ behaviour A ∘ PA.hom       ≈⟨ refl⟩∘⟨ Equiv.sym (pullʳ P∞.p₁∘universal≈h₁) ⟩
                R∞.π 0 ∘ P∞.diag ∘ P∞.universal _   ≈⟨ sym-assoc ⟩
                (R∞.π 0 ∘ P∞.diag) ∘ P∞.universal _ ∎
            }
            ; project₁ = P∞.p₁∘universal≈h₁
            ; project₂ = P∞.p₂∘universal≈h₂
            ; unique = λ a b → Equiv.sym (P∞.unique a b)
            }
        }
    }

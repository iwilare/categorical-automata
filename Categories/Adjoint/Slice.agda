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

module Categories.Adjoint.Slice {o l e o′ l′ e′} {K : Category o l e} {H : Category o′ l′ e′}
        (let module K = Category K)
        (let module H = Category H)
        (G : Functor K H)
        (U : Functor H K)
        (G⊣U : G ⊣ U)
        (A : H.Obj)
        (let module G = Functor G)
        (let module U = Functor U)
        (let module G⊣U = Adjoint G⊣U) where

    cod : ∀ {o l e} {K : Category o l e} {A} {X Y : SliceObj K A} → (a : Slice⇒ K {A} X Y) → SliceObj K A
    cod {X = X} {Y} _ = Y

    dom : ∀ {o l e} {K : Category o l e}  {A} {X Y : SliceObj K A} → (a : Slice⇒ K {A} X Y) → SliceObj K A
    dom {X = X} {Y} _ = X

    G~ : Functor (Slice K (U.₀ A)) (Slice H A)
    G~ = record
      { F₀ = λ { (sliceobj X) → sliceobj (G⊣U.Radjunct X) }
      ; F₁ = λ { arr@(slicearr {h = h} f) → slicearr {h = G.₁ h}
      let open Category H
          open MR H
          open H.HomReasoning in
          begin
              (G⊣U.counit.η A ∘ G.₁ (SliceObj.arr (cod arr))) ∘ G.₁ h ≈⟨ pullʳ (Equiv.sym G.homomorphism) ⟩
              G⊣U.counit.η A ∘ G.₁ (SliceObj.arr (cod arr) K.∘ h)      ≈⟨ refl⟩∘⟨ G.F-resp-≈ f ⟩
              G⊣U.counit.η A ∘ G.₁ (SliceObj.arr (dom arr))            ∎ }
      ; identity = G.identity
      ; homomorphism = G.homomorphism
      ; F-resp-≈ = G.F-resp-≈
      }

    U~ : Functor (Slice H A) (Slice K (U.₀ A))
    U~ = record
      { F₀ = λ { (sliceobj X) → sliceobj (U.₁ X) }
      ; F₁ = λ { arr@(slicearr {h = h} f) → slicearr {h = U.₁ h}
      let open Category K
          open MR K
          open K.HomReasoning in
        begin
          U.₁ (SliceObj.arr (cod arr)) ∘ U.₁ h ≈⟨ Equiv.sym U.homomorphism ⟩
          U.₁ (SliceObj.arr (cod arr) H.∘ h) ≈⟨ U.F-resp-≈ f ⟩
          U.₁ (SliceObj.arr (dom arr)) ∎ }
      ; identity = U.identity
      ; homomorphism = U.homomorphism
      ; F-resp-≈ = U.F-resp-≈
      }

    G⊣U~ : G~ ⊣ U~
    G⊣U~ = record
      { unit = ntHelper record
        { η = λ { (sliceobj {Y} A) → slicearr {h = G⊣U.unit.η Y}
        let open Category K
            open MR K
            open K.HomReasoning in
          begin
            U.₁ (G⊣U.counit.η _ H.∘ G.₁ A) ∘ G⊣U.unit.η Y ≈⟨ pushˡ U.homomorphism ⟩
            U.₁ (G⊣U.counit.η _) ∘ U.₁ (G.₁ A) ∘ G⊣U.unit.η Y ≈⟨ (refl⟩∘⟨ Equiv.sym (G⊣U.unit.commute _)) ⟩
            U.F₁ (G⊣U.counit.η _) ∘ G⊣U.unit.η (U.₀ _) ∘ A ≈⟨ sym-assoc ⟩
            (U.F₁ (G⊣U.counit.η _) ∘ G⊣U.unit.η (U.₀ _)) ∘ A ≈⟨ elimˡ G⊣U.zag ⟩
            A ∎ }
        ; commute = λ (slicearr {h = h} _) → G⊣U.unit.commute h
        }
      ; counit = ntHelper record
        { η = λ { (sliceobj {Y} A) → slicearr {h = G⊣U.counit.η Y} (H.Equiv.sym (G⊣U.counit.commute _)) }
        ; commute = λ (slicearr {h = h} _) → G⊣U.counit.commute h
        }
      ; zig = G⊣U.zig
      ; zag = G⊣U.zag
      }

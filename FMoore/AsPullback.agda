{-# OPTIONS --allow-unsolved-metas #-}

import Categories.Category.Complete
import Categories.Category.Construction.Cones as Co
import Categories.Morphism.Reasoning as MR
import Function as Fun
open import Axiom.UniquenessOfIdentityProofs using (UIP)
open import Categories.Adjoint
open import Categories.Adjoint
open import Categories.Category
open import Categories.Category using (Category; _[_,_])
open import Categories.Category.Complete
open import Categories.Category.Complete using (Complete)
open import Categories.Category.Complete.Finitely using (FinitelyComplete)
open import Categories.Category.Complete.Properties using (Complete⇒FinitelyComplete)
open import Categories.Category.Construction.Comma
open import Categories.Category.Construction.Comma
open import Categories.Category.Construction.F-Algebras
open import Categories.Category.Instance.Cats
open import Categories.Category.Instance.Properties.Setoids.Complete
open import Categories.Category.Instance.Setoids
open import Categories.Category.Instance.StrictCats
open import Categories.Category.Slice
open import Categories.Category.StrictCatsPullbacks
open import Categories.Diagram.Pullback
open import Categories.Functor renaming (id to idF)
open import Categories.Functor.Algebra
open import Categories.Functor.Equivalence
open import Categories.Category.Equivalence using (StrongEquivalence)
open import Categories.Functor.Slice
open import Categories.Morphism
open import Categories.NaturalTransformation using (ntHelper; NaturalTransformation)
open import Categories.NaturalTransformation using (ntHelper)
open import Categories.Object.Product
open import Categories.Object.Product.Indexed
open import Categories.Object.Terminal
open import Data.Product
open import Data.Product using (Σ; proj₁; proj₂; _,_; Σ-syntax; _×_; -,_)
open import Data.Unit
open import Function.Equality using (Π)
open import Level
open import Relation.Binary using (Setoid; Rel)
open import Relation.Binary.PropositionalEquality as E using ()
open NaturalTransformation
open Categories.Functor.Functor

module FMoore.AsPullback {o} {C : Category o o o} {F : Functor C C} (I : Category.Obj C) (O : Category.Obj C) where

open Category C
open HomReasoning
open Equiv
pattern * = lift Data.Unit.tt

open import FMoore F O

U : Functor (F-Algebras F) C
U = record
    { F₀ = F-Algebra.A
    ; F₁ = F-Algebra-Morphism.f
    ; identity = refl
    ; homomorphism = refl
    ; F-resp-≈ = λ F → F
    }

V : Functor (Slice C O) C
V = record
    { F₀ = λ (sliceobj {Y} h) → Y
    ; F₁ = λ (slicearr {h = h} c) → h
    ; identity = refl
    ; homomorphism = refl
    ; F-resp-≈ = λ x → x
    }

module PB = Pullback (Cats-Pullback {o = o} {ℓ = o} {e = o} U V)

asPullback : StrongEquivalence PB.P FMoore
asPullback = record
  { F = record
    { F₀ = λ { ((record { A = A ; α = α } , sliceobj arr) , E.refl) → record
      { E = A
      ; d = α
      ; s = arr
      } }
    ; F₁ = λ { {(a , a') , E.refl} {(b , b') , E.refl} ((record { f = f ; commutes = commutes } , slicearr {h = h} △) , fs≈sh) → record
      { hom = h
      ; comm-d = let eq : f ≈ h
                     eq = Equiv.trans (Equiv.sym identityʳ) (Equiv.trans fs≈sh identityˡ) in begin
        h ∘ F-Algebra.α a ≈⟨ Equiv.sym eq ⟩∘⟨refl ⟩
        f ∘ F-Algebra.α a ≈⟨ commutes ⟩
        F-Algebra.α b ∘ F₁ F f ≈⟨ refl⟩∘⟨ F-resp-≈ F eq ⟩
        F-Algebra.α b ∘ F₁ F h ∎
      ; comm-s = Equiv.sym △
      } }
    ; identity = λ { {_ , E.refl} → Equiv.refl }
    ; homomorphism = λ { {_ , E.refl} {_ , E.refl} {_ , E.refl} → Equiv.refl }
    ; F-resp-≈ = λ { {_ , E.refl} {_ , E.refl} (_ , b) → b }
    }
  ; G = record
    { F₀ = λ { record { E = E ; d = d ; s = s } →
       (record { A = E ; α = d }
       , sliceobj s)
       , E.refl }
    ; F₁ = λ { f → let module f = FMoore⇒ f in
       (record { f = f.hom ; commutes = f.comm-d }
       , slicearr (Equiv.sym f.comm-s))
       , MR.id-comm C }
    ; identity     = Equiv.refl , Equiv.refl
    ; homomorphism = Equiv.refl , Equiv.refl
    ; F-resp-≈ = λ fg → (fg , fg)
    }
  ; weak-inverse = record
    { F∘G≈id = record
      { F⇒G = ntHelper record
        { η = λ X → FMoore.id {X}
        ; commute = λ _ → MR.id-comm-sym C
        }
      ; F⇐G = ntHelper record
        { η = λ X → FMoore.id {X}
        ; commute = λ _ → MR.id-comm-sym C
        }
      ; iso = λ X → record
        { isoˡ = identity²
        ; isoʳ = identity²
        }
      }
    ; G∘F≈id = record
      { F⇒G = ntHelper record
        { η = λ { ((record { A = A ; α = α } , sliceobj arr) , E.refl)
                → (F-Algebras.id , Slice.id) , Equiv.refl }
        ; commute = λ { {_ , E.refl} {_ , E.refl} ((a , s) , e) → Equiv.sym e , MR.id-comm-sym C }
        }
      ; F⇐G = ntHelper record
        { η = λ { ((record { A = A ; α = α } , sliceobj arr) , E.refl)
                → (F-Algebras.id , Slice.id) , Equiv.refl }
        ; commute = λ { {_ , E.refl} {_ , E.refl} ((a , s) , e) → Equiv.trans (MR.id-comm-sym C) (Equiv.trans e (MR.id-comm-sym C)) , MR.id-comm-sym C } --Equiv.sym e , MR.id-comm-sym C } --λ _ → MR.id-comm-sym C
        }
      ; iso = λ { (_ , E.refl) → record
        { isoˡ = identity² , identity²
        ; isoʳ = identity² , identity²
        } }
      }
    }
  } where module FMoore = Category FMoore
          module Slice = Category (Slice C O)
          module F-Algebras = Category (F-Algebras F)

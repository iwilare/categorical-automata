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

open import Categories.Morphism.HeterogeneousIdentity
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

module PullbackFiberedAdjunctions {o}
          {A  : Category o o o} (let module A  = Category A )
          {K  : Category o o o} (let module K  = Category K )
          {B  : Category o o o} (let module B  = Category B )
          {B′ : Category o o o} (let module B′ = Category B′)
          {AK  : Functor A K}   (let module AK  = Functor AK)
          {BK  : Functor B  K}  (let module BK  = Functor BK)
          {B′K : Functor B′ K}  (let module B′K = Functor B′K)
          {F   : Functor B B′ } (let module F   = Functor F)
          {G   : Functor B′ B } (let module G   = Functor G)
          {tri₁ : BK ∘F G ≡F B′K}
          {tri₂ : B′K ∘F F ≡F BK}
          {F⊣G : F ⊣ G}  (let module F⊣G = Adjoint F⊣G) where

-- Face behind the square
module M′ = Pullback (Cats-Pullback {o = o} {ℓ = o} {e = o} AK B′K)

-- Face in front of the square
module M = Pullback (Cats-Pullback {o = o} {ℓ = o} {e = o} AK BK)

module StrictCats = Category (StrictCats o o o)

-- Front-to-back
MF : Functor M.P M′.P
MF = M′.universal {h₁ = M.p₁} {h₂ = F ∘F M.p₂}
       (trans M.commute (trans (sym tri₂ ⟩∘⟨refl) (StrictCats.assoc {g = F} {h = B′K})))
        where open StrictCats.Equiv
              open StrictCats.HomReasoning

-- Back-to-front
MG : Functor M′.P M.P
MG = M.universal {h₁ = M′.p₁} {h₂ = G ∘F M′.p₂}
       (trans M′.commute (trans (sym tri₁ ⟩∘⟨refl) (StrictCats.assoc {g = G} {h = BK})))
        where open StrictCats.Equiv
              open StrictCats.HomReasoning

PulledbackAdjunction : MF ⊣ MG
PulledbackAdjunction = record
  { unit = ntHelper record
    { η = λ { ((a , b) , Y) → (A.id , F⊣G.unit.η _) , _ }
    ; commute = λ { ((a , b) , f) → AMR.id-comm-sym ,  F⊣G.unit.commute b }
    }
  ; counit = ntHelper record
    { η = λ { ((a , b) , Y) → (A.id , F⊣G.counit.η _) , _ }
    ; commute = λ { ((a , b) , f) → AMR.id-comm-sym ,  F⊣G.counit.commute b }
    }
  ; zig = A.identity² , F⊣G.zig
  ; zag = A.identity² , F⊣G.zag
  } where module AMR = MR A
          open MR K
          open K.Equiv

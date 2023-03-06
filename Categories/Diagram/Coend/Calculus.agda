{-# OPTIONS --without-K #-}

module Categories.Diagram.Coend.Calculus where

open import Data.Nat using (ℕ; suc)
open import Data.Vec using (Vec; []; _∷_)

open import Categories.Category.BinaryProducts using (BinaryProducts)
open import Categories.Category.Cartesian
open import Categories.Category.Cartesian.Monoidal
open import Categories.Category.Construction.Functors
open import Categories.Category.Core using (Category)
open import Categories.Category.Equivalence
open import Categories.Category.Equivalence.Preserves
open import Categories.Category.Instance.Cats
open import Categories.Category.Instance.One renaming (One to ⊤)
open import Categories.Category.Monoidal
open import Categories.Category.Monoidal.Instance.Cats
open import Categories.Category.Product
open import Categories.Diagram.Coend
open import Categories.Diagram.Colimit
open import Categories.Diagram.Cowedge
open import Categories.Diagram.Cowedge.Properties
open import Categories.Functor using (Functor)
open import Categories.Functor.Bifunctor using (Bifunctor)
open import Categories.Functor.Instance.Twisted
open import Categories.NaturalTransformation hiding (id)
open import Categories.NaturalTransformation.Dinatural
open import Categories.Object.Initial as Initial
open import Categories.NaturalTransformation hiding (id)
open import Categories.NaturalTransformation.Dinatural

open import Categories.Tactic.Products as TP
open import Categories.Tactic.Category as TC

import Categories.Category.Construction.Cowedges as Cowedges
import Categories.Morphism
import Categories.Morphism.Reasoning as MR

open import Level renaming (suc to sucℓ)
open import Data.Product using (Σ; _,_) renaming (_×_ to _∧_)
open import Function using (_$_)

module _ {ℓ} {E : Category ℓ ℓ ℓ} where

  module E = Category E
  open Categories.Morphism (Cats ℓ ℓ ℓ)
  open _≅_
  module F {C} {D} = Categories.Morphism (Functors {ℓ} {ℓ} {ℓ} {ℓ} {ℓ} {ℓ} C D)

  open BinaryProducts (Product.Cats-has-all {ℓ} {ℓ} {ℓ})

  data Pos : Set (sucℓ ℓ) where
    ⁺ : Pos
    ⁻ : Pos
    ` : Pos

  Ctx = Vec (Category ℓ ℓ ℓ ∧ Pos)

  PosΓ : Category ℓ ℓ ℓ → Pos → Category ℓ ℓ ℓ
  PosΓ C ⁺ = C
  PosΓ C ⁻ = Category.op C
  PosΓ C ` = C × Category.op C

  PosΓ-cong : ∀ {C D P}
            → C ≅ D
            → PosΓ C P ≅ PosΓ D P
  PosΓ-cong {P = ⁺} C≅D = C≅D
  PosΓ-cong {P = ⁻} C≅D = {!   !}
  PosΓ-cong {P = `} C≅D = {!   !}

  CΓ : ∀ {n} → (Γ : Ctx n) → Category ℓ ℓ ℓ
  CΓ [] = E
  CΓ ((C , P) ∷ Γ) = Functors (PosΓ C P) (CΓ Γ)

  σ-Γ : ∀ {A B n} {Γ : Ctx n}
        → CΓ (A ∷ B ∷ Γ)
        ≅ CΓ (B ∷ A ∷ Γ)
  σ-Γ = {!   !}

  ⊗-Γ : ∀ {A B P n} {Γ : Ctx n}
        → CΓ ((A , P) ∷ (B , P) ∷ Γ)
        ≅ CΓ ((A × B , P) ∷ Γ)
  ⊗-Γ = {!   !}

  FΓ : ∀ {n} → Ctx n → Set _
  FΓ Γ = Functor (⊤ {ℓ} {ℓ} {ℓ}) (CΓ Γ)

  transport-CF : ∀ {n} {Γ Δ : Ctx n}
        → (t : CΓ Γ ≅ CΓ Δ)
        → {F : FΓ Γ}
          {G : FΓ Δ}
        → F F.≅ {!   !}
  transport-CF = {!   !}

  coend : ∀ {A n} {Γ : Ctx n}
        → FΓ (A ∷ Γ)
        → FΓ Γ
  coend F = {!  !}

  fubini : ∀ {A B n} {Γ : Ctx n}
             {F : FΓ (A ∷ B ∷ Γ) }
         → coend (coend F)
       F.≅ coend {! (⊗-Γ) .isoˡ !}
  fubini = {!   !}

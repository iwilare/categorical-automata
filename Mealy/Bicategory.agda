{-# OPTIONS --allow-unsolved-metas #-}

open import Level
open import Categories.Category
open import Categories.Bicategory
open import Categories.Functor renaming (id to idF)
open Categories.Functor.Functor
open import Categories.Functor.Construction.Constant
import Categories.Morphism.Reasoning as MR
open import Categories.Category.BinaryProducts
  using (BinaryProducts; module BinaryProducts)
open import Categories.Object.Terminal
open import Categories.NaturalTransformation using (ntHelper)
open import Categories.NaturalTransformation.NaturalIsomorphism
open import Categories.Category.Cartesian.Monoidal
open import Categories.Category.Monoidal

open import Categories.Category.Cartesian.Bundle

-- The bicategory of Mealy machines
module Mealy.Bicategory {o l e} (C : CartesianCategory o l e) where

open import Mealy C

open CartesianCategory C
open HomReasoning
open Terminal terminal
open BinaryProducts products

module Helpers where

  private
    variable
      A B D X Y Z : Obj
      f f′ g g′ h i : A ⇒ B

  open import Categories.Object.Product U

  ⁂-congˡ : f ≈ g → f ⁂ i ≈ g ⁂ i
  ⁂-congˡ a = [ product ⇒ product ]×-cong₂ a Equiv.refl

  ⁂-congʳ : f ≈ g → i ⁂ f ≈ i ⁂ g
  ⁂-congʳ = [ product ⇒ product ]×-cong₂ Equiv.refl

  ⁂-id : ∀ {A B} → (id {A = A}) ⁂ (id {A = B}) ≈ id
  ⁂-id = id×id product

  first∘⁂ : first f ∘ (f′ ⁂ g′) ≈ (f ∘ f′ ⁂ g′)
  first∘⁂ = Equiv.trans first∘⟨⟩ (⟨⟩-congʳ sym-assoc)

  second∘⁂ : second g ∘ (f′ ⁂ g′) ≈ (f′ ⁂ g ∘ g′)
  second∘⁂ = Equiv.trans second∘⟨⟩ (⟨⟩-congˡ sym-assoc)

  assocˡ∘second : ∀ {A B} → assocˡ {A = A} {B = B} ∘ (id ⁂ f) ≈ (id ⁂ (id ⁂ f)) ∘ assocˡ
  assocˡ∘second {f = f} =
    begin
      assocˡ ∘ (id ⁂ f)
    ≈˘⟨ refl⟩∘⟨ ⁂-congˡ ⁂-id ⟩
      assocˡ ∘ ((id ⁂ id) ⁂ f)
    ≈⟨ assocˡ∘⁂ ⟩
      (id ⁂ (id ⁂ f)) ∘ assocˡ
    ∎

  assocʳ∘first : ∀ {B C} → assocʳ {B = B} {C = C} ∘ (f ⁂ id) ≈ ((f ⁂ id) ⁂ id) ∘ assocʳ
  assocʳ∘first {f = f} =
    begin
      assocʳ ∘ (f ⁂ id)
    ≈˘⟨ refl⟩∘⟨ ⁂-congʳ ⁂-id ⟩
      assocʳ ∘ (f ⁂ (id ⁂ id))
    ≈⟨ assocʳ∘⁂ ⟩
      ((f ⁂ id) ⁂ id) ∘ assocʳ
    ∎

  second∘assocʳ : ∀ {A B} → (id ⁂ f) ∘ assocʳ {A = A} {B = B} ≈ assocʳ ∘ (id ⁂ (id ⁂ f))
  second∘assocʳ {f = f} =
    begin
      (id ⁂ f) ∘ assocʳ
    ≈˘⟨ ⁂-congˡ ⁂-id ⟩∘⟨refl  ⟩
      ((id ⁂ id) ⁂ f) ∘ assocʳ
    ≈˘⟨ assocʳ∘⁂ ⟩
      assocʳ ∘ (id ⁂ (id ⁂ f))
    ∎

  first∘assocˡ : ∀ {B C} → (f ⁂ id) ∘ assocˡ {B = B} {C = C} ≈ assocˡ ∘ ((f ⁂ id) ⁂ id)
  first∘assocˡ {f = f} =
    begin
      (f ⁂ id) ∘ assocˡ
    ≈˘⟨ ⁂-congʳ ⁂-id ⟩∘⟨refl ⟩
      (f ⁂ (id ⁂ id)) ∘ assocˡ
    ≈˘⟨ assocˡ∘⁂ ⟩
      assocˡ ∘ ((f ⁂ id) ⁂ id)
    ∎

open Helpers

module Cartesian-Monoidal = Monoidal (Categories.Category.Cartesian.Monoidal.CartesianMonoidal.monoidal cartesian)

open import Categories.Morphism.Reasoning U
open import Categories.Morphism U

import Categories.Object.Product.Core as P
open import Data.Product as PP using (_,_)
import Categories.Category.Product as CP

⊚ : ∀ {X Y Z} → Functor (CP.Product (Mealy Y Z) (Mealy X Y)) (Mealy X Z)
⊚ = record
  { F₀ = λ { (A , B) →
    let module A = MealyObj A
        module B = MealyObj B in
      record
        { E = A.E × B.E
        ; d = ⟨ A.d ∘ second B.s , B.d ∘ π₂ ⟩ ∘ assocˡ
        ; s = A.s ∘ second B.s ∘ assocˡ
        }}
  ; F₁ =
  λ { {A₁ PP., A₂} {B₁ PP., B₂} (f PP., g) →
    let module A₁ = MealyObj A₁
        module A₂ = MealyObj A₂
        module B₁ = MealyObj B₁
        module B₂ = MealyObj B₂
        module f = Mealy⇒ f
        module g = Mealy⇒ g in
      record
        { hom = f.hom ⁂ g.hom
        ; comm-d = begin
          (f.hom ⁂ g.hom) ∘ ⟨ A₁.d ∘ second A₂.s , A₂.d ∘ π₂ ⟩ ∘ assocˡ                                             ≈⟨ pullˡ ⁂∘⟨⟩ ⟩
          ⟨ f.hom ∘ A₁.d ∘ second A₂.s                               , g.hom ∘ A₂.d ∘ π₂ ⟩ ∘ assocˡ                  ≈⟨ ⟨⟩-congʳ  (refl⟩∘⟨ refl⟩∘⟨ ⁂-congʳ g.comm-s) ⟩∘⟨refl ⟩
          ⟨ f.hom ∘ A₁.d ∘ (id ⁂ (B₂.s ∘ first g.hom))               , g.hom ∘ A₂.d ∘ π₂ ⟩ ∘ assocˡ                  ≈⟨ ⟨⟩-congʳ  (refl⟩∘⟨ refl⟩∘⟨ Equiv.sym second∘second) ⟩∘⟨refl ⟩
          ⟨ f.hom ∘ A₁.d ∘ (id ⁂ B₂.s) ∘ (id ⁂ (g.hom ⁂ id))        , g.hom ∘ A₂.d ∘ π₂ ⟩ ∘ assocˡ                  ≈⟨ ⟨⟩-congʳ  (extendʳ f.comm-d) ⟩∘⟨refl ⟩
          ⟨ B₁.d ∘ (f.hom ⁂ id) ∘ (id ⁂ B₂.s) ∘ (id ⁂ (g.hom ⁂ id)) , g.hom ∘ A₂.d ∘ π₂ ⟩ ∘ assocˡ                ≈⟨ ⟨⟩-congʳ  (refl⟩∘⟨ pullˡ first∘second) ⟩∘⟨refl ⟩
          ⟨ B₁.d ∘ (f.hom ⁂ B₂.s) ∘ (id ⁂ (g.hom ⁂ id))             , g.hom ∘ A₂.d ∘ π₂ ⟩ ∘ assocˡ                ≈⟨ ⟨⟩-cong₂  (refl⟩∘⟨ ⁂∘⁂) sym-assoc ⟩∘⟨refl ⟩
          ⟨ B₁.d ∘ ((f.hom ∘ id) ⁂ (B₂.s ∘ (g.hom ⁂ id)))           , (g.hom ∘ A₂.d) ∘ π₂ ⟩ ∘ assocˡ                ≈⟨ ⟨⟩-cong₂  (refl⟩∘⟨ ⁂-congˡ identityʳ) (pushˡ g.comm-d) ⟩∘⟨refl ⟩
          ⟨ B₁.d ∘ (f.hom ⁂ B₂.s ∘ (g.hom ⁂ id))                    , B₂.d ∘ (g.hom ⁂ id) ∘ π₂ ⟩ ∘ assocˡ           ≈⟨ ⟨⟩-cong₂ (pushʳ (Equiv.sym second∘⁂)) (pushʳ (Equiv.sym π₂∘⁂)) ⟩∘⟨refl ⟩
          ⟨ (B₁.d ∘ second B₂.s) ∘ (f.hom ⁂ (g.hom ⁂ id))           , (B₂.d ∘ π₂) ∘ (f.hom ⁂ g.hom ⁂ id) ⟩ ∘ assocˡ ≈⟨ pushˡ (Equiv.sym ⟨⟩∘) ⟩
          ⟨ B₁.d ∘ second B₂.s , B₂.d ∘ π₂ ⟩ ∘ (f.hom ⁂ (g.hom ⁂ id)) ∘ assocˡ                                      ≈˘⟨ refl⟩∘⟨ assocˡ∘⁂ ⟩
          ⟨ B₁.d ∘ second B₂.s , B₂.d ∘ π₂ ⟩ ∘ assocˡ ∘ ((f.hom ⁂ g.hom) ⁂ id)                                      ≈⟨ sym-assoc ⟩
          (⟨ B₁.d ∘ second B₂.s , B₂.d ∘ π₂ ⟩ ∘ assocˡ) ∘ ((f.hom ⁂ g.hom) ⁂ id)                                    ∎
        ; comm-s = begin
          A₁.s ∘ (id ⁂ A₂.s) ∘ assocˡ                            ≈⟨ pushˡ f.comm-s ⟩
          B₁.s ∘ (f.hom ⁂ id) ∘ (id ⁂ A₂.s) ∘ assocˡ             ≈⟨ refl⟩∘⟨ pullˡ ⁂∘⁂ ⟩
          B₁.s ∘ ((f.hom ∘ id) ⁂ (id ∘ A₂.s)) ∘ assocˡ           ≈⟨ refl⟩∘⟨ ⁂-congˡ id-comm ⟩∘⟨refl ⟩
          B₁.s ∘ ((id ∘ f.hom) ⁂ (id ∘ A₂.s)) ∘ assocˡ           ≈⟨ refl⟩∘⟨ ⁂-congʳ identityˡ ⟩∘⟨refl ⟩
          B₁.s ∘ ((id ∘ f.hom) ⁂ A₂.s) ∘ assocˡ                  ≈⟨ refl⟩∘⟨ ⁂-congʳ g.comm-s ⟩∘⟨refl ⟩
          B₁.s ∘ ((id ∘ f.hom) ⁂ (B₂.s ∘ (g.hom ⁂ id))) ∘ assocˡ ≈⟨ refl⟩∘⟨ pushˡ (Equiv.sym ⁂∘⁂) ⟩
          B₁.s ∘ (id ⁂ B₂.s) ∘ (f.hom ⁂ (g.hom ⁂ id)) ∘ assocˡ   ≈˘⟨ refl⟩∘⟨ refl⟩∘⟨ assocˡ∘⁂ ⟩
          B₁.s ∘ (id ⁂ B₂.s) ∘ assocˡ ∘ ((f.hom ⁂ g.hom) ⁂ id)   ≈⟨ refl⟩∘⟨ sym-assoc ⟩
          B₁.s ∘ ((id ⁂ B₂.s) ∘ assocˡ) ∘ ((f.hom ⁂ g.hom) ⁂ id) ≈⟨ sym-assoc ⟩
          (B₁.s ∘ (id ⁂ B₂.s) ∘ assocˡ) ∘ ((f.hom ⁂ g.hom) ⁂ id) ∎
        } }
  ; identity     = ⁂-id
  ; homomorphism = Equiv.sym ⁂∘⁂
  ; F-resp-≈     = λ (f₁≈g₁ , f₂≈g₂) → ⁂-cong₂ f₁≈g₁ f₂≈g₂
  }

π₂∘assocˡ : ∀ {A B C} → π₂ {A = C} {B = A × B} ∘ assocˡ ≈ π₂ ⁂ id
π₂∘assocˡ = begin π₂ ∘ assocˡ ≈⟨ project₂ ⟩ ⟨ π₂ ∘ π₁ , π₂ ⟩ ≈˘⟨ ⟨⟩-congˡ identityˡ ⟩ π₂ ⁂ id ∎

MealyBicategory : Bicategory (o ⊔ l ⊔ e) (o ⊔ l ⊔ e) e o
MealyBicategory = record
  { enriched = record
    { Obj = Obj
    ; hom = Mealy
    ; id = const (record
      { E = ⊤
      ; d = !
      ; s = π₂
      })
    ; ⊚ = ⊚
    ; ⊚-assoc =
      record
      { F⇒G = ntHelper record
        { η = λ { ((X PP., Y) PP., Z) →
         let module X = MealyObj X in
         let module Y = MealyObj Y in
         let module Z = MealyObj Z in
         let lemma1 : assocˡ ∘ (id ⁂ Z.s) ∘ assocˡ -- todo: refactor comm-s with this
                     ≈ (id ⁂ (id ⁂ Z.s)) ∘ (id ⁂ assocˡ) ∘ assocˡ ∘ (assocˡ ⁂ id)
             lemma1 = begin
               assocˡ ∘ (id ⁂ Z.s) ∘ assocˡ ≈⟨ extendʳ assocˡ∘second  ⟩
               (id ⁂ (id ⁂ Z.s)) ∘ assocˡ ∘ assocˡ ≈˘⟨ refl⟩∘⟨ Cartesian-Monoidal.pentagon ⟩
               (id ⁂ (id ⁂ Z.s)) ∘ (id ⁂ assocˡ) ∘ assocˡ ∘ (assocˡ ⁂ id) ∎ in
         let lemma2 : π₂ ∘ assocˡ ∘ (id ⁂ Z.s) ∘ assocˡ
                   ≈ (id ⁂ Z.s) ∘ assocˡ ∘ π₂ ∘ assocˡ ∘ (assocˡ ⁂ id)
             lemma2 = begin
                 π₂ ∘ assocˡ ∘ (id ⁂ Z.s) ∘ assocˡ ≈⟨ refl⟩∘⟨ lemma1 ⟩
                 π₂ ∘ (id ⁂ (id ⁂ Z.s)) ∘ (id ⁂ assocˡ) ∘ assocˡ ∘ (assocˡ ⁂ id) ≈⟨ extendʳ project₂ ⟩
                 (id ⁂ Z.s) ∘ π₂ ∘ (id ⁂ assocˡ) ∘ assocˡ ∘ (assocˡ ⁂ id) ≈⟨ refl⟩∘⟨ extendʳ project₂ ⟩
                 (id ⁂ Z.s) ∘ assocˡ ∘ π₂ ∘ assocˡ ∘ (assocˡ ⁂ id) ∎ in
         let lemma3 :  π₂ ∘ assocˡ ≈ π₂ ∘ assocˡ ∘ π₂ ∘ assocˡ ∘ (assocˡ ⁂ id)
             lemma3 = begin
                 π₂ ∘ assocˡ ≈⟨ introˡ ⁂-id ⟩
                 (id ⁂ id) ∘ π₂ ∘ assocˡ ≈⟨ extendʳ (Equiv.sym project₂) ⟩
                 π₂ ∘ (π₂ ⁂ (id ⁂ id)) ∘ assocˡ ≈⟨ refl⟩∘⟨ Equiv.sym assocˡ∘⁂ ⟩
                 π₂ ∘ assocˡ ∘ ((π₂ ⁂ id) ⁂ id) ≈⟨ refl⟩∘⟨ refl⟩∘⟨ ⁂-congˡ (Equiv.sym π₂∘assocˡ) ⟩
                 π₂ ∘ assocˡ ∘ ((π₂ ∘ assocˡ) ⁂ id) ≈⟨ refl⟩∘⟨ refl⟩∘⟨ Equiv.sym first∘first ⟩
                 π₂ ∘ assocˡ ∘ (π₂ ⁂ id) ∘ (assocˡ ⁂ id) ≈⟨ refl⟩∘⟨ refl⟩∘⟨ pushˡ (Equiv.sym π₂∘assocˡ) ⟩
                 π₂ ∘ assocˡ ∘ π₂ ∘ assocˡ ∘ (assocˡ ⁂ id) ∎ in
         record
          { hom = assocˡ
          ; comm-d = begin
            assocˡ ∘ ⟨ (⟨ X.d ∘ (id ⁂ Y.s) , Y.d ∘ π₂ ⟩ ∘ assocˡ) ∘ (id ⁂ Z.s) , Z.d ∘ π₂ ⟩ ∘ assocˡ ≈⟨ refl⟩∘⟨ ⟨⟩∘ ⟩
            assocˡ ∘ ⟨ ((⟨ X.d ∘ (id ⁂ Y.s) , Y.d ∘ π₂ ⟩ ∘ assocˡ) ∘ (id ⁂ Z.s)) ∘ assocˡ , (Z.d ∘ π₂) ∘ assocˡ ⟩ ≈⟨ refl⟩∘⟨ ⟨⟩-cong₂ (Equiv.trans assoc assoc) assoc ⟩
            assocˡ ∘ ⟨ ⟨ X.d ∘ (id ⁂ Y.s) , Y.d ∘ π₂ ⟩ ∘ assocˡ ∘ (id ⁂ Z.s) ∘ assocˡ , Z.d ∘ π₂ ∘ assocˡ ⟩ ≈⟨ ⟨⟩∘ ⟩
            ⟨ (π₁ ∘ π₁) ∘ ⟨ _ , _ ⟩ , ⟨ π₂ ∘ π₁ , π₂ ⟩ ∘ ⟨ _ , _ ⟩ ⟩ ≈⟨ ⟨⟩-cong₂ (pullʳ project₁) (⟨⟩-congˡ (Equiv.sym identityˡ) ⟩∘⟨refl) ⟩
            ⟨ π₁ ∘ ⟨ _ , _ ⟩ ∘ _ , ⟨ π₂ ∘ π₁ , id ∘ π₂ ⟩ ∘ ⟨ _ , _ ⟩ ⟩ ≈⟨ ⟨⟩-cong₂ (pullˡ project₁) first∘⟨⟩ ⟩
            ⟨ (X.d ∘ (id ⁂ Y.s)) ∘ assocˡ ∘ (id ⁂ Z.s) ∘ assocˡ , ⟨ π₂ ∘ _ , _ ⟩ ⟩ ≈⟨ ⟨⟩-cong₂ assoc (⟨⟩-congʳ (pullˡ project₂)) ⟩
            ⟨ X.d ∘ (id ⁂ Y.s) ∘ assocˡ ∘ (id ⁂ Z.s) ∘ assocˡ ,
             ⟨ (Y.d ∘ π₂) ∘ assocˡ ∘ (id ⁂ Z.s) ∘ assocˡ
             , Z.d ∘ π₂ ∘ assocˡ ⟩ ⟩ ≈⟨ ⟨⟩-congˡ (⟨⟩-congʳ assoc) ⟩
            ⟨ X.d ∘ (id ⁂ Y.s) ∘ assocˡ ∘ (id ⁂ Z.s) ∘ assocˡ ,
             ⟨ Y.d ∘ π₂ ∘ assocˡ ∘ (id ⁂ Z.s) ∘ assocˡ
             , Z.d ∘ π₂ ∘ assocˡ ⟩ ⟩ ≈⟨ ⟨⟩-cong₂ (refl⟩∘⟨ refl⟩∘⟨ lemma1) (⟨⟩-cong₂ (refl⟩∘⟨ lemma2) (refl⟩∘⟨ lemma3)) ⟩
            ⟨ X.d ∘ (id ⁂ Y.s) ∘ (id ⁂ (id ⁂ Z.s)) ∘ (id ⁂ assocˡ) ∘ assocˡ ∘ (assocˡ ⁂ id)
            , ⟨ Y.d ∘ (id ⁂ Z.s) ∘ assocˡ ∘ π₂ ∘ assocˡ ∘ (assocˡ ⁂ id)
            , Z.d ∘ π₂ ∘ assocˡ ∘ π₂ ∘ assocˡ ∘ (assocˡ ⁂ id) ⟩ ⟩ ≈⟨ ⟨⟩-congˡ (⟨⟩-cong₂ sym-assoc sym-assoc) ⟩
            ⟨ X.d ∘ (id ⁂ Y.s) ∘ (id ⁂ (id ⁂ Z.s)) ∘ (id ⁂ assocˡ) ∘ assocˡ ∘ (assocˡ ⁂ id)
            , ⟨ (Y.d ∘ (id ⁂ Z.s)) ∘ assocˡ ∘ π₂ ∘ assocˡ ∘ (assocˡ ⁂ id)
            , (Z.d ∘ π₂) ∘ assocˡ ∘ π₂ ∘ assocˡ ∘ (assocˡ ⁂ id) ⟩ ⟩ ≈⟨ ⟨⟩-congˡ (Equiv.sym ⟨⟩∘) ⟩
            ⟨ X.d ∘ (id ⁂ Y.s) ∘ (id ⁂ (id ⁂ Z.s)) ∘ (id ⁂ assocˡ) ∘ assocˡ ∘ (assocˡ ⁂ id)
            , ⟨ Y.d ∘ (id ⁂ Z.s)
            , Z.d ∘ π₂ ⟩ ∘ assocˡ ∘ π₂ ∘ assocˡ ∘ (assocˡ ⁂ id) ⟩ ≈⟨ ⟨⟩-congʳ (refl⟩∘⟨ refl⟩∘⟨ pullˡ second∘second) ⟩
            ⟨ X.d ∘ (id ⁂ Y.s) ∘ (id ⁂ ((id ⁂ Z.s) ∘ assocˡ)) ∘ assocˡ ∘ (assocˡ ⁂ id)
            , ⟨ Y.d ∘ (id ⁂ Z.s) , Z.d ∘ π₂ ⟩ ∘ assocˡ ∘ π₂ ∘ assocˡ ∘ (assocˡ ⁂ id) ⟩ ≈⟨ ⟨⟩-congʳ (refl⟩∘⟨ pullˡ second∘second ) ⟩
            ⟨ X.d ∘ (id ⁂ Y.s ∘ (id ⁂ Z.s) ∘ assocˡ) ∘ assocˡ ∘ (assocˡ ⁂ id)
            , ⟨ Y.d ∘ (id ⁂ Z.s) , Z.d ∘ π₂ ⟩ ∘ assocˡ ∘ π₂ ∘ assocˡ ∘ (assocˡ ⁂ id) ⟩ ≈˘⟨ ⟨⟩-cong₂ assoc (Equiv.trans assoc assoc) ⟩
            ⟨ (X.d ∘ (id ⁂ Y.s ∘ (id ⁂ Z.s) ∘ assocˡ)) ∘ assocˡ ∘ (assocˡ ⁂ id)
            , ((⟨ Y.d ∘ (id ⁂ Z.s) , Z.d ∘ π₂ ⟩ ∘ assocˡ) ∘ π₂) ∘ assocˡ ∘ (assocˡ ⁂ id) ⟩ ≈˘⟨ ⟨⟩∘ ⟩
            ⟨ X.d ∘ (id ⁂ (Y.s ∘ (id ⁂ Z.s) ∘ assocˡ)) , (⟨ Y.d ∘ (id ⁂ Z.s) , Z.d ∘ π₂ ⟩ ∘ assocˡ) ∘ π₂ ⟩ ∘ assocˡ ∘ (assocˡ ⁂ id) ≈˘⟨ assoc ⟩
            (⟨ X.d ∘ (id ⁂ (Y.s ∘ (id ⁂ Z.s) ∘ assocˡ)) , (⟨ Y.d ∘ (id ⁂ Z.s) , Z.d ∘ π₂ ⟩ ∘ assocˡ) ∘ π₂ ⟩ ∘ assocˡ) ∘ (assocˡ ⁂ id) ∎
          ; comm-s = begin
            (X.s ∘ (id ⁂ Y.s) ∘ assocˡ) ∘ (id ⁂ Z.s) ∘ assocˡ                             ≈⟨ Equiv.trans assoc (refl⟩∘⟨ assoc) ⟩
            X.s ∘ (id ⁂ Y.s) ∘ assocˡ ∘ (id ⁂ Z.s) ∘ assocˡ                               ≈⟨ refl⟩∘⟨ refl⟩∘⟨ extendʳ assocˡ∘second ⟩
            X.s ∘ (id ⁂ Y.s) ∘ (id ⁂ (id ⁂ Z.s)) ∘ assocˡ ∘ assocˡ                        ≈˘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ Cartesian-Monoidal.pentagon ⟩
            X.s ∘ (id ⁂ Y.s) ∘ (id ⁂ (id ⁂ Z.s)) ∘ (id ⁂ assocˡ) ∘ assocˡ ∘ (assocˡ ⁂ id) ≈⟨ refl⟩∘⟨ refl⟩∘⟨ pullˡ second∘second ⟩
            X.s ∘ (id ⁂ Y.s) ∘ (id ⁂ ((id ⁂ Z.s) ∘ assocˡ)) ∘ assocˡ ∘ (assocˡ ⁂ id)      ≈⟨ refl⟩∘⟨ pullˡ second∘second ⟩
            X.s ∘ (id ⁂ (Y.s ∘ (id ⁂ Z.s) ∘ assocˡ)) ∘ assocˡ ∘ (assocˡ ⁂ id)             ≈˘⟨ Equiv.trans assoc (refl⟩∘⟨ assoc) ⟩
            (X.s ∘ (id ⁂ (Y.s ∘ (id ⁂ Z.s) ∘ assocˡ)) ∘ assocˡ) ∘ (assocˡ ⁂ id)           ∎
          } }
        ; commute = λ ((X PP., Y) PP., Z) → assocˡ∘⁂
        }
      ; F⇐G = ntHelper record
        { η = λ { ((X PP., Y) PP., Z) →
         let module X = MealyObj X in
         let module Y = MealyObj Y in
         let module Z = MealyObj Z in
         let lemma4 : π₂ ∘ assocˡ ∘ π₂ ∘ assocˡ ≈ ((π₂ ∘ π₂) ⁂ id)
             lemma4 = begin
              π₂ ∘ assocˡ ∘ π₂ ∘ assocˡ ≈⟨ refl⟩∘⟨ refl⟩∘⟨ π₂∘assocˡ ⟩
              π₂ ∘ assocˡ ∘ (π₂ ⁂ id) ≈⟨ pullˡ π₂∘assocˡ ⟩
              (π₂ ⁂ id) ∘ (π₂ ⁂ id) ≈⟨ first∘first ⟩
              ((π₂ ∘ π₂) ⁂ id) ∎ in
         let lemma5 : (id ⁂ Z.s) ∘ assocˡ ∘ π₂ ∘ assocˡ
                    ≈ π₂ ∘ (id ⁂ id ⁂ Z.s) ∘ (id ⁂ assocˡ) ∘ assocˡ
             lemma5 =  begin
              (id ⁂ Z.s) ∘ assocˡ ∘ π₂ ∘ assocˡ ≈˘⟨ refl⟩∘⟨ extendʳ π₂∘⁂ ⟩
              (id ⁂ Z.s) ∘ π₂ ∘ (id ⁂ assocˡ) ∘ assocˡ ≈⟨ extendʳ (Equiv.sym project₂) ⟩
              π₂ ∘ (id ⁂ (id ⁂ Z.s)) ∘ (id ⁂ assocˡ) ∘ assocˡ ∎ in
         record
          { hom = assocʳ
          ; comm-d = begin
            assocʳ ∘ ⟨ X.d ∘ (id ⁂ (Y.s ∘ (id ⁂ Z.s) ∘ assocˡ)) , (⟨ Y.d ∘ (id ⁂ Z.s) , Z.d ∘ π₂ ⟩ ∘ assocˡ) ∘ π₂ ⟩ ∘ assocˡ ≈⟨ refl⟩∘⟨ ⟨⟩∘ ⟩
            assocʳ ∘ ⟨ (X.d ∘ (id ⁂ (Y.s ∘ (id ⁂ Z.s) ∘ assocˡ))) ∘ assocˡ , ((⟨ Y.d ∘ (id ⁂ Z.s) , Z.d ∘ π₂ ⟩ ∘ assocˡ) ∘ π₂) ∘ assocˡ ⟩  ≈⟨ refl⟩∘⟨ ⟨⟩-cong₂ assoc (Equiv.trans assoc assoc) ⟩
            assocʳ ∘ ⟨ X.d ∘ (id ⁂ (Y.s ∘ (id ⁂ Z.s) ∘ assocˡ)) ∘ assocˡ , ⟨ Y.d ∘ (id ⁂ Z.s) , Z.d ∘ π₂ ⟩ ∘ assocˡ ∘ π₂ ∘ assocˡ ⟩  ≈⟨ ⟨⟩∘ ⟩
            ⟨ ⟨ π₁ , π₁ ∘ π₂ ⟩ ∘ ⟨ _ , _ ⟩ , (π₂ ∘ π₂) ∘ ⟨ _ , _ ⟩ ⟩ ≈⟨ ⟨⟩-cong₂ (⟨⟩-congʳ (Equiv.sym identityˡ) ⟩∘⟨refl) (pullʳ project₂) ⟩
            ⟨ (id ⁂ π₁) ∘ ⟨ _ , _ ⟩ , π₂ ∘ _ ⟩                       ≈⟨ ⟨⟩-cong₂ second∘⟨⟩ (pullˡ project₂) ⟩
            ⟨ ⟨ X.d ∘ (id ⁂ Y.s ∘ (id ⁂ Z.s) ∘ assocˡ) ∘ assocˡ , π₁ ∘ ⟨ Y.d ∘ (id ⁂ Z.s) , Z.d ∘ π₂ ⟩ ∘ assocˡ ∘ π₂ ∘ assocˡ ⟩
            , (Z.d ∘ π₂) ∘ assocˡ ∘ π₂ ∘ assocˡ ⟩ ≈⟨ ⟨⟩-cong₂ (⟨⟩-congˡ (pullˡ project₁)) (pullʳ lemma4) ⟩
            ⟨ ⟨ X.d ∘ (id ⁂ Y.s ∘ (id ⁂ Z.s) ∘ assocˡ) ∘ assocˡ
              , (Y.d ∘ (id ⁂ Z.s)) ∘ assocˡ ∘ π₂ ∘ assocˡ ⟩
            , Z.d ∘ ((π₂ ∘ π₂) ⁂ id) ⟩ ≈⟨ ⟨⟩-congʳ (⟨⟩-cong₂ (refl⟩∘⟨ pushˡ (Equiv.sym second∘second)) assoc) ⟩
            ⟨ ⟨ X.d ∘ (id ⁂ Y.s) ∘ (id ⁂ ((id ⁂ Z.s) ∘ assocˡ)) ∘ assocˡ
              , Y.d ∘ (id ⁂ Z.s) ∘ assocˡ ∘ π₂ ∘ assocˡ ⟩
            , Z.d ∘ ((π₂ ∘ π₂) ⁂ id) ⟩ ≈⟨ ⟨⟩-congʳ (⟨⟩-cong₂ (refl⟩∘⟨ refl⟩∘⟨ pushˡ (Equiv.sym second∘second)) (refl⟩∘⟨ lemma5)) ⟩
            ⟨ ⟨ X.d ∘ (id ⁂ Y.s) ∘ (id ⁂ (id ⁂ Z.s)) ∘ (id ⁂ assocˡ) ∘ assocˡ
              , Y.d ∘ π₂ ∘ (id ⁂ id ⁂ Z.s) ∘ (id ⁂ assocˡ) ∘ assocˡ ⟩
            , Z.d ∘ ((π₂ ∘ π₂) ⁂ id) ⟩ ≈⟨ ⟨⟩-congʳ (⟨⟩-cong₂ sym-assoc sym-assoc) ⟩
            ⟨ ⟨ (X.d ∘ (id ⁂ Y.s)) ∘ (id ⁂ id ⁂ Z.s) ∘ (id ⁂ assocˡ) ∘ assocˡ
              , (Y.d ∘ π₂) ∘ (id ⁂ id ⁂ Z.s) ∘ (id ⁂ assocˡ) ∘ assocˡ ⟩
            , Z.d ∘ ((π₂ ∘ π₂) ⁂ id) ⟩ ≈⟨ ⟨⟩-congʳ (Equiv.sym ⟨⟩∘) ⟩
            ⟨ ⟨ X.d ∘ (id ⁂ Y.s) , Y.d ∘ π₂ ⟩ ∘ (id ⁂ id ⁂ Z.s) ∘ (id ⁂ assocˡ) ∘ assocˡ
            , Z.d ∘ ((π₂ ∘ π₂) ⁂ id) ⟩ ≈⟨ ⟨⟩-congʳ (refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ introʳ (Equiv.trans (⁂-congˡ assocˡ∘assocʳ) ⁂-id)) ⟩
            ⟨ ⟨ X.d ∘ (id ⁂ Y.s) , Y.d ∘ π₂ ⟩ ∘ (id ⁂ id ⁂ Z.s) ∘ (id ⁂ assocˡ) ∘ assocˡ ∘ ((assocˡ ∘ assocʳ) ⁂ id)
            , Z.d ∘ ((π₂ ∘ π₂) ⁂ id) ⟩ ≈⟨ ⟨⟩-congʳ (refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ Equiv.sym first∘first) ⟩
            ⟨ ⟨ X.d ∘ (id ⁂ Y.s) , Y.d ∘ π₂ ⟩ ∘ (id ⁂ id ⁂ Z.s) ∘ (id ⁂ assocˡ) ∘ assocˡ ∘ (assocˡ ⁂ id) ∘ (assocʳ ⁂ id)
            , Z.d ∘ ((π₂ ∘ π₂) ⁂ id) ⟩
              ≈˘⟨ ⟨⟩-cong₂ (refl⟩∘⟨ refl⟩∘⟨ Equiv.trans assoc (refl⟩∘⟨ assoc)) (refl⟩∘⟨ ⁂-congˡ project₂) ⟩
            ⟨ ⟨ X.d ∘ (id ⁂ Y.s) , Y.d ∘ π₂ ⟩ ∘ (id ⁂ id ⁂ Z.s) ∘ ((id ⁂ assocˡ) ∘ assocˡ ∘ (assocˡ ⁂ id)) ∘ (assocʳ ⁂ id)
            , Z.d ∘ (π₂ ∘ assocʳ ⁂ id) ⟩
              ≈˘⟨ ⟨⟩-cong₂ (refl⟩∘⟨ refl⟩∘⟨ Equiv.sym Cartesian-Monoidal.pentagon ⟩∘⟨refl) (refl⟩∘⟨ first∘first) ⟩
            ⟨ ⟨ X.d ∘ (id ⁂ Y.s) , Y.d ∘ π₂ ⟩ ∘ (id ⁂ id ⁂ Z.s) ∘ (assocˡ ∘ assocˡ) ∘ (assocʳ ⁂ id)
            , Z.d ∘ (π₂ ⁂ id) ∘ (assocʳ ⁂ id) ⟩
              ≈⟨ ⟨⟩-congʳ (refl⟩∘⟨ refl⟩∘⟨ assoc) ⟩
            ⟨ ⟨ X.d ∘ (id ⁂ Y.s) , Y.d ∘ π₂ ⟩ ∘ (id ⁂ id ⁂ Z.s) ∘ assocˡ ∘ assocˡ ∘ (assocʳ ⁂ id)
            , Z.d ∘ (π₂ ⁂ id) ∘ (assocʳ ⁂ id) ⟩
              ≈⟨ ⟨⟩-congʳ (refl⟩∘⟨ extendʳ (Equiv.sym assocˡ∘second)) ⟩
            ⟨ ⟨ X.d ∘ (id ⁂ Y.s) , Y.d ∘ π₂ ⟩ ∘ assocˡ ∘ (id ⁂ Z.s) ∘ assocˡ ∘ (assocʳ ⁂ id)
            , Z.d ∘ (π₂ ⁂ id) ∘ (assocʳ ⁂ id) ⟩
              ≈˘⟨ ⟨⟩-cong₂ (Equiv.trans assoc (refl⟩∘⟨ assoc)) (pullʳ (pullˡ π₂∘assocˡ)) ⟩
            ⟨ (⟨ X.d ∘ (id ⁂ Y.s) , Y.d ∘ π₂ ⟩ ∘ assocˡ ∘ (id ⁂ Z.s)) ∘ assocˡ ∘ (assocʳ ⁂ id)
            , (Z.d ∘ π₂) ∘ assocˡ ∘ (assocʳ ⁂ id) ⟩
              ≈⟨ Equiv.sym ⟨⟩∘ ⟩
            ⟨ ⟨ X.d ∘ (id ⁂ Y.s) , Y.d ∘ π₂ ⟩ ∘ assocˡ ∘ (id ⁂ Z.s) , Z.d ∘ π₂ ⟩ ∘ assocˡ ∘ (assocʳ ⁂ id)     ≈˘⟨ ⟨⟩-congʳ assoc ⟩∘⟨refl ⟩
            ⟨ (⟨ X.d ∘ (id ⁂ Y.s) , Y.d ∘ π₂ ⟩ ∘ assocˡ) ∘ (id ⁂ Z.s) , Z.d ∘ π₂ ⟩ ∘ assocˡ ∘ (assocʳ ⁂ id)   ≈˘⟨ assoc ⟩
            (⟨ (⟨ X.d ∘ (id ⁂ Y.s) , Y.d ∘ π₂ ⟩ ∘ assocˡ) ∘ (id ⁂ Z.s) , Z.d ∘ π₂ ⟩ ∘ assocˡ) ∘ (assocʳ ⁂ id) ∎
          ; comm-s = begin
            X.s ∘ (id ⁂ (Y.s ∘ (id ⁂ Z.s) ∘ assocˡ)) ∘ assocˡ                                               ≈⟨ refl⟩∘⟨ pushˡ (Equiv.sym second∘second) ⟩
            X.s ∘ (id ⁂ Y.s) ∘ (id ⁂ ((id ⁂ Z.s) ∘ assocˡ)) ∘ assocˡ                                        ≈⟨ refl⟩∘⟨ refl⟩∘⟨ pushˡ (Equiv.sym second∘second) ⟩
            X.s ∘ (id ⁂ Y.s) ∘ (id ⁂ (id ⁂ Z.s)) ∘ (id ⁂ assocˡ) ∘ assocˡ                                   ≈⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ introʳ ⁂-id ⟩
            X.s ∘ (id ⁂ Y.s) ∘ (id ⁂ (id ⁂ Z.s)) ∘ (id ⁂ assocˡ) ∘ assocˡ ∘ (id ⁂ id)                       ≈˘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ ⁂-congˡ assocˡ∘assocʳ ⟩
            X.s ∘ (id ⁂ Y.s) ∘ (id ⁂ (id ⁂ Z.s)) ∘ (id ⁂ assocˡ) ∘ assocˡ ∘ ((assocˡ ∘ assocʳ) ⁂ id)        ≈˘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ first∘first ⟩
            X.s ∘ (id ⁂ Y.s) ∘ (id ⁂ (id ⁂ Z.s)) ∘ (id ⁂ assocˡ) ∘ assocˡ ∘ (assocˡ ⁂ id) ∘ (assocʳ ⁂ id)   ≈˘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ Equiv.trans assoc (refl⟩∘⟨ assoc) ⟩
            X.s ∘ (id ⁂ Y.s) ∘ (id ⁂ (id ⁂ Z.s)) ∘ ((id ⁂ assocˡ) ∘ assocˡ ∘ (assocˡ ⁂ id)) ∘ (assocʳ ⁂ id) ≈˘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ pullˡ (Equiv.sym Cartesian-Monoidal.pentagon) ⟩
            X.s ∘ (id ⁂ Y.s) ∘ (id ⁂ (id ⁂ Z.s)) ∘ assocˡ ∘ assocˡ ∘ (assocʳ ⁂ id)                          ≈˘⟨ refl⟩∘⟨ refl⟩∘⟨ extendʳ assocˡ∘second ⟩
            X.s ∘ (id ⁂ Y.s) ∘ assocˡ ∘ (id ⁂ Z.s) ∘ assocˡ ∘ (assocʳ ⁂ id) ≈˘⟨ Equiv.trans assoc (Equiv.trans (refl⟩∘⟨ assoc) (Equiv.trans assoc (refl⟩∘⟨ assoc))) ⟩
            ((X.s ∘ (id ⁂ Y.s) ∘ assocˡ) ∘ (id ⁂ Z.s) ∘ assocˡ) ∘ (assocʳ ⁂ id) ∎
          } }
        ; commute = λ ((X PP., Y) PP., Z) → assocʳ∘⁂
        }
      ; iso = λ X → record { isoˡ = assocʳ∘assocˡ ; isoʳ = assocˡ∘assocʳ }
      }
    ; unitˡ = record
      { F⇒G = ntHelper record
        { η = λ (_ PP., X) →
          let module X = MealyObj X in
          let lemma : π₂ ∘ assocˡ ≈ π₂ ⁂ id
              lemma = begin
                π₂ ∘ assocˡ           ≈⟨ project₂ ⟩
                ⟨ π₂ ∘ π₁ , π₂ ⟩      ≈⟨ ⟨⟩-congˡ (Equiv.sym identityˡ) ⟩
                ⟨ π₂ ∘ π₁ , id ∘ π₂ ⟩ ∎ in
          record
          { hom = π₂
          ; comm-d = begin
            π₂ ∘ ⟨ ! ∘ ⟨ id ∘ π₁ , X.s ∘ π₂ ⟩ , X.d ∘ π₂ ⟩ ∘ assocˡ ≈⟨ extendʳ project₂ ⟩
            X.d ∘ π₂ ∘ assocˡ                                       ≈⟨ refl⟩∘⟨ lemma ⟩
            X.d ∘ ⟨ π₂ ∘ π₁ , id ∘ π₂ ⟩                             ∎
          ; comm-s = begin
            π₂ ∘ ⟨ id ∘ π₁ , X.s ∘ π₂ ⟩ ∘ assocˡ ≈⟨ extendʳ project₂ ⟩
            X.s ∘ π₂ ∘ assocˡ                    ≈⟨ refl⟩∘⟨ lemma ⟩
            X.s ∘ ⟨ π₂ ∘ π₁ , id ∘ π₂ ⟩          ∎
          }
        ; commute = λ _ → project₂
        }
      ; F⇐G = ntHelper record
        { η = λ (_ PP., X) →
          let module X = MealyObj X in record
          { hom = ⟨ ! , id ⟩
          ; comm-d = begin
            ⟨ ! , id ⟩ ∘ X.d ≈⟨ ⟨⟩∘ ⟩
            ⟨ ! ∘ X.d , id ∘ X.d ⟩ ≈⟨ ⟨⟩-congˡ id-comm-sym ⟩
            ⟨ ! ∘ X.d , X.d ∘ id ⟩  ≈⟨ ⟨⟩-cong₂ (Equiv.sym (!-unique _)) (refl⟩∘⟨ Equiv.sym ⁂-id) ⟩
            ⟨ ! , X.d ∘ ⟨ id ∘ π₁ , id ∘ π₂ ⟩ ⟩ ≈⟨ ⟨⟩-cong₂ (!-unique _) (Equiv.sym (pullʳ project₂)) ⟩
            ⟨ (! ∘ (id ⁂ X.s)) ∘ ⟨ ! ∘ π₁ , ⟨ id ∘ π₁ , id ∘ π₂ ⟩ ⟩ , (X.d ∘ π₂) ∘ ⟨ ! ∘ π₁ , ⟨ id ∘ π₁ , id ∘ π₂ ⟩ ⟩ ⟩ ≈⟨ Equiv.sym ⟨⟩∘ ⟩
            ⟨ ! ∘ (id ⁂ X.s) , X.d ∘ π₂ ⟩ ∘ ⟨ ! ∘ π₁ , ⟨ id ∘ π₁ , id ∘ π₂ ⟩ ⟩              ≈⟨ Equiv.sym (pullʳ assocˡ∘⟨⟩) ⟩
            (⟨ ! ∘ (id ⁂ X.s) , X.d ∘ π₂ ⟩ ∘ assocˡ) ∘ (⟨ ⟨ ! ∘ π₁ , id ∘ π₁ ⟩ , id ∘ π₂ ⟩) ≈˘⟨ refl⟩∘⟨ ⟨⟩-congʳ ⟨⟩∘ ⟩
            (⟨ ! ∘ (id ⁂ X.s) , X.d ∘ π₂ ⟩ ∘ assocˡ) ∘ (⟨ ! , id ⟩ ⁂ id)                    ∎
          ; comm-s = begin
            X.s ≈⟨ introʳ ⁂-id ⟩
            X.s ∘ ⟨ id ∘ π₁ , id ∘ π₂ ⟩                                               ≈˘⟨ refl⟩∘⟨ project₂ ⟩
            X.s ∘ π₂ ∘ ⟨ ! ∘ π₁ , ⟨ id ∘ π₁ , id ∘ π₂ ⟩ ⟩                             ≈˘⟨ extendʳ project₂ ⟩
            π₂ ∘ ⟨ id ∘ π₁ , X.s ∘ π₂ ⟩ ∘ ⟨ ! ∘ π₁ , ⟨ id ∘ π₁ , id ∘ π₂ ⟩ ⟩          ≈˘⟨ refl⟩∘⟨ refl⟩∘⟨ assocˡ∘⟨⟩ ⟩
            π₂ ∘ ⟨ id ∘ π₁ , X.s ∘ π₂ ⟩ ∘ assocˡ ∘ ⟨ ⟨ ! ∘ π₁ , id ∘ π₁ ⟩ , id ∘ π₂ ⟩ ≈˘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ ⟨⟩-congʳ ⟨⟩∘ ⟩
            π₂ ∘ ⟨ id ∘ π₁ , X.s ∘ π₂ ⟩ ∘ assocˡ ∘ (⟨ ! , id ⟩ ⁂ id)                  ≈˘⟨ Equiv.trans assoc (refl⟩∘⟨ assoc) ⟩
            (π₂ ∘ ⟨ id ∘ π₁ , X.s ∘ π₂ ⟩ ∘ assocˡ) ∘ (⟨ ! , id ⟩ ⁂ id)                ∎
          }
        ; commute = λ (_ PP., f) →
          let module f = Mealy⇒ f in begin
            ⟨ ! , id ⟩ ∘ f.hom         ≈⟨ ⟨⟩∘ ⟩
            ⟨ ! ∘ f.hom , id ∘ f.hom ⟩ ≈⟨ ⟨⟩-cong₂ (Equiv.trans (Equiv.sym (!-unique _)) (Equiv.sym identityˡ)) id-comm-sym ⟩
            ⟨ id ∘ ! , f.hom ∘ id ⟩    ≈˘⟨ ⁂∘⟨⟩ ⟩
            (id ⁂ f.hom) ∘ ⟨ ! , id ⟩  ∎
        }
      ; iso = λ X → record { isoˡ = begin
            ⟨ ! , id ⟩ ∘ π₂ ≈⟨ ⟨⟩∘ ⟩
            ⟨ ! ∘ π₂ , id ∘ π₂ ⟩ ≈⟨ unique !-unique₂ id-comm ⟩
            id ∎ ; isoʳ = project₂ }
      }
    ; unitʳ = record
      { F⇒G = ntHelper record
        { η = λ (X PP., _) →
          let module X = MealyObj X in
          let lemma6 : (id ⁂ π₂) ∘ assocˡ ≈ (π₁ ⁂ id)
              lemma6 = begin
                ⟨ id ∘ π₁ , π₂ ∘ π₂ ⟩ ∘ assocˡ           ≈⟨ ⁂∘⟨⟩ ⟩
                ⟨ id ∘ π₁ ∘ π₁ , π₂ ∘ ⟨ π₂ ∘ π₁ , π₂ ⟩ ⟩ ≈⟨ ⟨⟩-cong₂ identityˡ (Equiv.trans project₂ (Equiv.sym identityˡ)) ⟩
                ⟨ π₁ ∘ π₁ , id ∘ π₂ ⟩ ∎ in
              record
          { hom = π₁
          ; comm-d = begin
            π₁ ∘ ⟨ X.d ∘ ⟨ id ∘ π₁ , π₂ ∘ π₂ ⟩ , ! ∘ π₂ ⟩ ∘ assocˡ ≈⟨ extendʳ project₁ ⟩
            X.d ∘ ⟨ id ∘ π₁ , π₂ ∘ π₂ ⟩ ∘ assocˡ ≈⟨ refl⟩∘⟨ lemma6 ⟩
            X.d ∘ ⟨ π₁ ∘ π₁ , id ∘ π₂ ⟩ ∎
          ; comm-s = begin
            X.s ∘ ⟨ id ∘ π₁ , π₂ ∘ π₂ ⟩ ∘ assocˡ ≈⟨ refl⟩∘⟨ lemma6 ⟩
            X.s ∘ ⟨ π₁ ∘ π₁ , id ∘ π₂ ⟩  ∎
          }
        ; commute = λ _ → project₁
        }
      ; F⇐G = ntHelper record
        { η = λ (X PP., _) →
          let module X = MealyObj X in record
          { hom = ⟨ id , ! ⟩
          ; comm-d = begin
            ⟨ id , ! ⟩ ∘ X.d ≈⟨ ⟨⟩∘ ⟩
            ⟨ id ∘ X.d , ! ∘ X.d ⟩ ≈⟨ ⟨⟩-congʳ id-comm-sym ⟩
            ⟨ X.d ∘ id , ! ∘ X.d ⟩ ≈⟨ ⟨⟩-congʳ (refl⟩∘⟨ Equiv.sym ⁂-id) ⟩
            ⟨ X.d ∘ ⟨ id ∘ π₁ , id ∘ π₂ ⟩ , ! ∘ X.d ⟩ ≈⟨ ⟨⟩-congʳ (refl⟩∘⟨ ⟨⟩-cong₂ (refl⟩∘⟨ Equiv.sym identityˡ) (Equiv.sym project₂)) ⟩
            ⟨ X.d ∘ ⟨ id ∘ id ∘ π₁ , π₂ ∘ ⟨ ! ∘ π₁ , id ∘ π₂ ⟩ ⟩  , ! ∘ X.d ⟩ ≈⟨ ⟨⟩-cong₂ (Equiv.sym (pullʳ ⁂∘⟨⟩)) !-unique₂ ⟩
            ⟨ (X.d ∘ ⟨ id ∘ π₁ , π₂ ∘ π₂ ⟩) ∘ ⟨ id ∘ π₁ , ⟨ ! ∘ π₁ , id ∘ π₂ ⟩ ⟩ , (! ∘ π₂) ∘ ⟨ id ∘ π₁ , ⟨ ! ∘ π₁ , id ∘ π₂ ⟩ ⟩ ⟩ ≈⟨ Equiv.sym ⟨⟩∘ ⟩
            ⟨ X.d ∘ (id ⁂ π₂) , ! ∘ π₂ ⟩ ∘ ⟨ id ∘ π₁ , ⟨ ! ∘ π₁ , id ∘ π₂ ⟩ ⟩ ≈⟨ Equiv.sym (pullʳ assocˡ∘⟨⟩) ⟩
            (⟨ X.d ∘ (id ⁂ π₂) , ! ∘ π₂ ⟩ ∘ assocˡ) ∘ ⟨ ⟨ id ∘ π₁ , ! ∘ π₁ ⟩ , id ∘ π₂ ⟩ ≈˘⟨ refl⟩∘⟨ ⟨⟩-congʳ ⟨⟩∘ ⟩
            (⟨ X.d ∘ (id ⁂ π₂) , ! ∘ π₂ ⟩ ∘ assocˡ) ∘ (⟨ id , ! ⟩ ⁂ id) ∎
          ; comm-s = begin
            X.s ≈⟨ introʳ ⁂-id ⟩
            X.s ∘ ⟨ id ∘ π₁ , id ∘ π₂ ⟩ ≈˘⟨ refl⟩∘⟨ ⟨⟩-cong₂ (pullˡ identity²) project₂ ⟩
            X.s ∘ ⟨ id ∘ id ∘ π₁ , π₂ ∘ ⟨ ! ∘ π₁ , id ∘ π₂ ⟩ ⟩ ≈˘⟨ refl⟩∘⟨ ⁂∘⟨⟩ ⟩
            X.s ∘ ⟨ id ∘ π₁ , π₂ ∘ π₂ ⟩ ∘ ⟨ id ∘ π₁ , ⟨ ! ∘ π₁ , id ∘ π₂ ⟩ ⟩ ≈˘⟨ refl⟩∘⟨ refl⟩∘⟨ assocˡ∘⟨⟩ ⟩
            X.s ∘ ⟨ id ∘ π₁ , π₂ ∘ π₂ ⟩ ∘ assocˡ ∘ ⟨ ⟨ id ∘ π₁ , ! ∘ π₁ ⟩ , id ∘ π₂ ⟩ ≈˘⟨ refl⟩∘⟨ refl⟩∘⟨ refl⟩∘⟨ ⟨⟩-congʳ ⟨⟩∘ ⟩
            X.s ∘ ⟨ id ∘ π₁ , π₂ ∘ π₂ ⟩ ∘ assocˡ ∘ ⟨ ⟨ id , ! ⟩ ∘ π₁ , id ∘ π₂ ⟩ ≈˘⟨ Equiv.trans assoc (refl⟩∘⟨ assoc) ⟩
            (X.s ∘  ⟨ id ∘ π₁ , π₂ ∘ π₂ ⟩ ∘ assocˡ) ∘ ⟨ ⟨ id , ! ⟩ ∘ π₁ , id ∘ π₂ ⟩ ∎
          }
        ; commute = λ (f PP., _) →
          let module f = Mealy⇒ f in begin
            ⟨ id , ! ⟩ ∘ f.hom         ≈⟨ ⟨⟩∘ ⟩
            ⟨ id ∘ f.hom , ! ∘ f.hom ⟩ ≈⟨ ⟨⟩-cong₂ id-comm-sym (Equiv.trans (Equiv.sym (!-unique _)) (Equiv.sym identityˡ)) ⟩
            ⟨ f.hom ∘ id  , id ∘ ! ⟩   ≈˘⟨ ⁂∘⟨⟩ ⟩
            (f.hom ⁂ id) ∘ ⟨ id , ! ⟩  ∎
        }
      ; iso = λ X → record
        { isoˡ =
         begin
           ⟨ id , ! ⟩ ∘ π₁ ≈⟨ ⟨⟩∘ ⟩
           ⟨ id ∘ π₁ , ! ∘ π₁ ⟩ ≈⟨ unique id-comm !-unique₂ ⟩
           id ∎
        ; isoʳ = project₁
        }
      }
    }
 ; triangle = Cartesian-Monoidal.triangle
 ; pentagon = Cartesian-Monoidal.pentagon
 }

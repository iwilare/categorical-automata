{-# OPTIONS --without-K --safe #-}

module Categories.Diagram.Coend.Properties where

open import Categories.Category.Core using (Category)
--open import Categories.Category.Product
import Categories.Category.Construction.Cowedges as Cowedges
open import Categories.Category.Construction.Functors
open import Categories.Category.Equivalence
open import Categories.Category.Equivalence.Preserves
open import Categories.Category.CartesianClosed
open import Categories.Category.Cartesian
open import Categories.Category.BinaryProducts
open import Categories.Diagram.Coend
open import Categories.Object.Product
open import Categories.Functor using (Functor; _∘F_) renaming (id to idF)
open Categories.Functor.Functor using (F₀; F₁; homomorphism; identity; F-resp-≈)
open import Categories.Diagram.Colimit
open import Categories.Diagram.Cowedge
open import Categories.Diagram.Cowedge.Properties
import Categories.Functor using (Functor)
open import Categories.Functor.Bifunctor using (Bifunctor)
open import Categories.Functor.Instance.Twisted
import Categories.Morphism as M
open import Categories.NaturalTransformation hiding (id)
open import Categories.NaturalTransformation.Dinatural
open import Categories.Object.Initial as Initial
open import Categories.Category.Instance.One renaming (One to ⊤)

import Categories.Morphism.Reasoning as MR

open import Level
open import Data.Product using (Σ; _,_)
open import Function using (_$_)

module _ {o ℓ e} {C : Category o ℓ e} (CC : CartesianClosed C) where
  module CC = CartesianClosed CC
  module P = Cartesian CC.cartesian
  open BinaryProducts P.products
  open Category C

  F : Obj → Bifunctor (Category.op C) C C
  F x = record
    { F₀ = λ (c , c') → (c CC.⇨ x) × c'
    ; F₁ = λ (f , f') → Functor.F₁ (CC.-⇨_ x) f ⁂ f'
    ; identity =
       begin _ ≈⟨ ⟨⟩-congˡ identityˡ ⟩
             _ ≈⟨ ⟨⟩-congʳ (elimˡ (identity (CC.-⇨ x))) ⟩
             _ ≈⟨ η ⟩
             _ ∎
    ; homomorphism = {!   !}
    ; F-resp-≈ = {!   !}
    } where open HomReasoning
            open MR C

  Coenda : ∀ x → Coend (F x)
  Coenda x = record
    { cowedge = record
      { E = x
      ; dinatural = record
        { α = λ c → CC.eval′
        ; commute = {!   !}
        ; op-commute = {!   !}
        }
      }
    ; factor = λ W →
        let module W = Cowedge W in
         {!  !}
    ; universal = {!   !}
    ; unique = {!   !}
    }


{-


-- ⟨⟩-cong

module _ {o ℓ e o′ ℓ′ e′} {C : Category o ℓ e} {D : Category o′ ℓ′ e′}
  (F : Bifunctor (Category.op C) C D) where
  open Cowedges F

  -- Being a Coend is the same as being an Initial object in the category of Cowedges
  Coend⇒Initial : Coend F → Initial Cowedges
  Coend⇒Initial c = record
    { ⊥ = cowedge
    ; ⊥-is-initial = record
      { ! = λ {A} → record { u = factor A ; commute = universal }
      ; !-unique = λ {A} f → unique {A} (Cowedge-Morphism.commute f)
      }
    }
    where
    open Coend c

  Initial⇒Coend : Initial Cowedges → Coend F
  Initial⇒Coend i = record
    { cowedge = ⊥
    ; factor = λ W → u {W₂ = W} !
    ; universal = commute !
    ; unique = λ {_} {g} x → !-unique (record { u = g ; commute = x })
    }
    where
    open Initial.Initial i
    open Cowedge-Morphism

private
  variable
    o ℓ e : Level
    C D E : Category o ℓ e

module _ (F : Functor E (Functors (Product (Category.op C) C) D)) where
  private
    module C = Category C
    module D = Category D
    module E = Category E
    module NT = NaturalTransformation
  open D
  open HomReasoning

  open MR D
  open Functor F
  open Coend hiding (E)
  open NT using (η)

  CoendF : (∀ X → Coend (F₀ X)) → Functor E D
  CoendF coend = record
    { F₀           = λ X → Coend.E (coend X)
    ; F₁           = F₁′
    ; identity     = λ {A} → unique (coend A) (id-comm-sym ○ ∘-resp-≈ʳ (⟺ identity))
    ; homomorphism = λ {A B C} {f g} → unique (coend A) $ λ {Z} → begin
      (F₁′ g ∘ F₁′ f) ∘ dinatural.α (coend A) Z                         ≈⟨  pullʳ (universal (coend A)) ⟩
      (F₁′ g ∘ (dinatural.α (coend B) Z ∘ η (F₁ f) (Z , Z) )  )         ≈⟨ pullˡ (universal (coend B))  ⟩
      ((dinatural.α (coend C) Z ∘ η (F₁ g) (Z , Z)) ∘ η (F₁ f) (Z , Z)) ≈˘⟨ pushʳ homomorphism ⟩
      dinatural.α (coend C) Z ∘ η (F₁ (g E.∘ f)) (Z , Z)                ∎
    ; F-resp-≈     = λ {A B f g} eq → unique (coend A) $ λ {Z} → begin
      F₁′ g ∘ dinatural.α (coend A) Z                               ≈⟨ universal (coend A) ⟩
      dinatural.α (coend B) Z ∘ η (F₁ g) (Z , Z)                   ≈˘⟨ refl⟩∘⟨ F-resp-≈ eq ⟩
      dinatural.α (coend B) Z ∘ η (F₁ f) (Z , Z)                   ∎
    }
    where F₁′ : ∀ {X Y} → X E.⇒ Y → Coend.E (coend X) ⇒ Coend.E (coend Y)
          F₁′ {X} {Y} f = factor (coend X) $ record
            { E         = Coend.E (coend Y)
            ; dinatural = dinatural (coend Y) ∘> F₁ f
            }

-- A Natural Transformation between two functors induces an arrow between the
-- (object part of) the respective coends.
module _ {P Q : Functor (Product (Category.op C) C) D} (P⇒Q : NaturalTransformation P Q) where
  open Coend renaming (E to coend)
  open Category D

  coend-η : {cp : Coend P} {cq : Coend Q} → coend cp ⇒ coend cq
  coend-η {cp} {cq} = factor cp ((record
    { E = Coend.E cq
    ; dinatural = dtHelper record
      { α = λ c →  dinatural.α cq c ∘ η (c , c)
      ; commute = λ {C} {C′} f → begin
        id ∘ (αq C ∘ η (C , C)) ∘ P.₁ (f , C.id)    ≈⟨ pushʳ assoc ⟩
        (id ∘ αq C) ∘ (η (C , C) ∘ P.₁ (f , C.id))  ≈⟨ refl⟩∘⟨ nt.commute (f , C.id) ⟩
        (id ∘ αq C) ∘ (Q.₁ (f , C.id) ∘ η (C′ , C)) ≈⟨ pullˡ assoc ⟩
        (id ∘ αq C ∘ Q.₁ (f , C.id)) ∘ η (C′ , C)   ≈⟨ αq-comm f ⟩∘⟨refl ⟩
        (id ∘ αq C′ ∘ Q.₁ (C.id , f)) ∘ η (C′ , C)  ≈⟨ pushˡ sym-assoc ⟩
        (id ∘ αq C′) ∘ Q.₁ (C.id , f) ∘ η (C′ , C)  ≈⟨ refl⟩∘⟨ nt.sym-commute (C.id , f) ⟩
        (id ∘ αq C′) ∘ η (C′ , C′) ∘ P.₁ (C.id , f) ≈⟨ pullʳ sym-assoc ⟩
        id ∘ (αq C′ ∘ η (C′ , C′)) ∘ P.₁ (C.id , f) ∎
      }
    }))
    where
    module nt = NaturalTransformation P⇒Q
    open nt using (η)
    open HomReasoning
    module C = Category C
    module P = Functor P
    module Q = Functor Q
    open DinaturalTransformation (dinatural cp) renaming (α to αp; commute to αp-comm)
    open DinaturalTransformation (dinatural cq) renaming (α to αq; commute to αq-comm)
    open Cowedge
    open MR D


{-
module _ {o ℓ e o′ ℓ′ e′} {C : Category o ℓ e} {D : Category o′ ℓ′ e′}  {E : Category o′ ℓ′ e′}
  (F : Bifunctor (Category.op C) C D) where
  private
    Eq = CoconesTwist≅Cowedges F
    module O = M D
  open M (Cowedges.Cowedges F)
  open Functor

  open StrongEquivalence Eq renaming (F to F⇒)

  -- Coends and Colimits are equivalent, in the category Cowedge F
  Coend-as-Colimit : (coend : Coend F) → (cl : Colimit (Twist′ C D F)) → Coend.cowedge coend ≅ F₀ F⇒ (Colimit.initial.⊥ cl)
  Coend-as-Colimit coend cl = Initial.up-to-iso (Cowedges.Cowedges F) (Coend⇒Initial F coend) (pres-Initial Eq initial)
    where
    open Colimit cl

  -- Which then induces that the objects, in D, are also equivalent.
  Coend-as-Colimit-on-Obj : (coend : Coend F) → (cl : Colimit (Twist′ C D F)) → Coend.E coend O.≅ Colimit.coapex cl
  Coend-as-Colimit-on-Obj coend cl = record
    { from = Cowedge-Morphism.u (M._≅_.from X≅Y)
    ; to = Cowedge-Morphism.u (M._≅_.to X≅Y)
    ; iso = record
      { isoˡ = M._≅_.isoˡ X≅Y
      ; isoʳ = M._≅_.isoʳ X≅Y
      }
    }
    where
      X≅Y = Coend-as-Colimit coend cl
      open Category D

  -- "transposes" of a F : (C x D).op x (C x D) -> E:
  -- F induces F' : C.op x C -> Functors (D.op x D) E
  --           F'' : D.op x D -> Functors (C.op x C) E
  -- let's write the helpers using `curry₀`:

  _ᵒᵒ : ∀ {o ℓ e} → Category o ℓ e → Category o ℓ e
  X ᵒᵒ = Product (Category.op X) X

  _′ : (F : Bifunctor (Category.op (Product C D)) (Product C D) E) → Functor (C ᵒᵒ) (Functors (D ᵒᵒ) E)
  F ′ = record
    { F₀ = λ {(c , c') →
      record
        { F₀ = λ {(d , d') → Functor.F₀ F (((c , d) , (c' , d')))}
        ; F₁ = λ { {a , a'} {b , b'} (f , f') → Functor.F₁ F ((_ , f) , (_ , f'))}
        ; identity = λ {A} → Functor.identity F
        ; homomorphism = λ {X} {Y} {Z} {f} {g} → {!   !}
        ; F-resp-≈ = λ x → {!   !}
        }}
    ; F₁ = λ { {a , a'} {b , b'} (f , f') →
      record { η = λ X → {!   !}
            ; commute = {!   !}
            ; sym-commute = {!   !}
            }}
    ; identity = {!   !}
    ; homomorphism = {!   !}
    ; F-resp-≈ = {!   !}
    }

  _′′ : (F : Bifunctor (Category.op (Product C D)) (Product C D) E) → Functor (D ᵒᵒ) (Functors (C ᵒᵒ) E)
  F ′′ = {!   !}


  Fubini : (F : Bifunctor (Category.op (Product C D)) (Product C D) E)
        → (allCoends : ∀ X → Coend (Functor.F₀ (F ′) X))
        → Coend (CoendF ( F ′) allCoends)
        → Coend F
  Fubini F AllCoends ∫∀ = record
    { cowedge = record
      { E = ∫∀.E
      ; dinatural = record
        { α = λ (c , d) → ∫∀.dinatural.α c ∘ ∫∀s.dinatural.α (c , c) d
        ; commute = λ (f , f') → begin _ ≈⟨ {!  ∫∀.dinatural.commute f !}  ⟩
                                {! _  !} ≈⟨ {!   !} ⟩
                                _ ∎
        ; op-commute = {!   !}
        }
      }
    ; factor = {!   !}
    ; universal = {!   !} ; unique = {!   !} }
    where module ∫∀ = Coend ∫∀
          module ∫∀s X = Coend (AllCoends X)
          open Category E
          open HomReasoning
-}
-}

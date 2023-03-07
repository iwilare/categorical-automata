
open import Level
open import Data.Product using (Σ; proj₁; proj₂; _,_; Σ-syntax; _×_; -,_)
open import Function.Equality using (Π)
open import Relation.Binary using (Setoid; Rel)

open import Categories.Category using (Category; _[_,_])
open import Categories.Functor
open import Categories.Category.Instance.Setoids
open import Categories.Category.Instance.Cats
open import Categories.Category.Complete

import Categories.Category.Construction.Cones as Co

open Π using (_⟨$⟩_)

module Categories.Category.CatsComplete where

Cats-Complete : {o ℓ e o' ℓ' e'  : Level} → Complete o ℓ e (Cats {!   !} {!   !} {!   !}) -- (suc (o ⊔ ℓ ⊔ e ⊔ ℓ')) (suc (o ⊔ ℓ ⊔ e ⊔ e'))) --(c ⊔ ℓ ⊔ o ⊔ ℓ′) (o ⊔ ℓ′))
Cats-Complete {o} {ℓ} {e} {o'} {ℓ'} {e'} {J = J} F =
  record
  { terminal = record
    { ⊤        = record
      { N     = record
        { Obj = Σ (∀ (j : Category {!   !} {!   !} {!   !}) → Category.Obj j) λ S → ∀ {X Y} (f : J [ X , Y ]) → {! Functor.₀ (F.₁ f) ?    !} --∀ {X Y} (F : Functor X Y) → {!  Functor.F₁ F   !}
        ; _⇒_ = λ { (S₁ , _) (S₂ , _) → ∀ (j : Category (o ⊔ ℓ ⊔ e) (o ⊔ ℓ ⊔ e) {!  o ⊔ ℓ' ⊔ e' !}) → Category._⇒_ j (S₁ j) (S₂ j) }
        ; _≈_ = λ { a b → ∀ (j : Category (o ⊔ ℓ ⊔ e) (o ⊔ ℓ ⊔ e) {!  o ⊔ ℓ ⊔ e !}) → Category._≈_ j (a j) (b j) }
        ; id = λ j → Category.id j
        ; _∘_ = λ x y j → Category._∘_ j (x j) (y j)
        ; assoc = {!   !}
        ; sym-assoc = {!   !}
        ; identityˡ = {!   !}
        ; identityʳ = {!   !}
        ; identity² = {!   !}
        ; equiv = {!   !}
        ; ∘-resp-≈ = {!   !}
        }
      ; apex = record
        { ψ = λ j → record
            { F₀ = λ (S , _) → {!   !} --λ (S , _) → S j
            ; F₁ = {!   !}
            ; identity = {!   !}
            ; homomorphism = {!   !}
            ; F-resp-≈ = {!   !}
            }
        ; commute = λ f → record
          { F⇒G = record { η = λ Y → {!   !} ; commute = {!   !} ; sym-commute = {!   !} }
          ; F⇐G = {!   !}
          ; iso = {!   !}
          }
        }
      --record
      --  { ψ = λ j → record
      --    { _⟨$⟩_ = λ { (S , _) → S j }
      --    ; cong  = λ eq → eq j
      --    }
      --  ; commute = λ { {X} {Y} X⇒Y {_ , eq} {y} f≈g → F₀.trans Y (eq X⇒Y) (f≈g Y) }
      --  }
      }
    ; ⊤-is-terminal = {!   !} {-record
      { !        = λ {K} →
        let module K = Cone K
        in record
        { arr     = record
          { _⟨$⟩_ = λ x → (λ j → K.ψ j ⟨$⟩ x) , λ f → K.commute f (Setoid.refl K.N)
          ; cong  = λ a≈b j → Π.cong (K.ψ j) a≈b
          }
        ; commute = λ x≈y → Π.cong (K.ψ _) x≈y
        }
      ; !-unique = λ {K} f x≈y j →
        let module K = Cone K
        in F₀.sym j (Cone⇒.commute f (Setoid.sym K.N x≈y))
      }
    -}
    }
  }
  where module F = Functor F
        module J = Category J
        open Co F

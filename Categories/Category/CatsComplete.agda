{-# OPTIONS --allow-unsolved-metas #-}

open import Level
open import Data.Product using (Σ; proj₁; proj₂; _,_; Σ-syntax; _×_; -,_)
open import Function.Equality using (Π)
open import Relation.Binary using (Setoid; Rel)

open import Categories.Category using (Category; _[_,_])
open import Categories.Functor
open import Categories.Category.Instance.Setoids
open import Categories.Category.Instance.Properties.Setoids.Complete
open import Categories.Category.Instance.Cats
open import Categories.Category.Complete
open import Categories.NaturalTransformation using (ntHelper)
open import Categories.Morphism

import Categories.Category.Construction.Cones as Co

open Π using (_⟨$⟩_)

module Categories.Category.CatsComplete where

Cats-Complete : {o ℓ e o' ℓ' e'  : Level} → Complete o ℓ e (Cats (o ⊔ ℓ) ((o ⊔ ℓ)) ((o ⊔ ℓ))) -- (suc (o ⊔ ℓ ⊔ e ⊔ ℓ')) (suc (o ⊔ ℓ ⊔ e ⊔ e'))) --(c ⊔ ℓ ⊔ o ⊔ ℓ′) (o ⊔ ℓ′))
Cats-Complete {o} {ℓ} {e} {o'} {ℓ'} {e'} {J = J} F =
  record
  { terminal = record
    { ⊤        = record
      { N     = record
        { Obj = Σ (∀ (j : J.Obj) → Category.Obj (F.₀ j))
                  λ S → ∀ {X Y} (f : J [ X , Y ])
                      → _≅_ (F.F₀ Y) (Functor.₀ (F.₁ f) (S X)) (S Y)
        ; _⇒_ = λ { (S₁ , _) (S₂ , _)
              → ∀ (j : J.Obj)
              → Category._⇒_ (F.₀ j) (S₁ j) (S₂ j) }
        ; _≈_ = λ { a b → ∀ (j : J.Obj)
                   → Category._≈_ (F.₀ j) (a j) (b j) }
        ; id = λ j → Category.id (F.₀ j)
        ; _∘_ = λ x y j → Category._∘_ (F.₀ j) (x j) (y j)
        ; assoc     = λ j → Category.assoc (F.₀ j)
        ; sym-assoc = λ j → Category.sym-assoc (F.₀ j)
        ; identityˡ = λ j → Category.identityˡ (F.₀ j)
        ; identityʳ = λ j → Category.identityʳ (F.₀ j)
        ; identity² = λ j → Category.identity² (F.₀ j)
        ; equiv     = record
          { refl  = λ j → Category.Equiv.refl (F.₀ j)
          ; sym   = λ f≈g j → Category.Equiv.sym (F.₀ j) (f≈g j)
          ; trans = λ f≈g g≈h j → Category.Equiv.trans (F.₀ j) (f≈g j) (g≈h j)
          }
        ; ∘-resp-≈  = λ f≈ g≈ j → Category.∘-resp-≈ (F.₀ j) (f≈ j) (g≈ j)
        }
      ; apex = record
        { ψ = λ j → record
            { F₀ = λ (S , _) → S j
            ; F₁ = λ f → f j
            ; identity = Category.Equiv.refl (F.₀ j)
            ; homomorphism = Category.Equiv.refl (F.₀ j)
            ; F-resp-≈ = λ f≈g → f≈g j
            }
        ; commute = λ X⇒Y → record
          { F⇒G = ntHelper record
            { η = λ { (S , e) → _≅_.from (e X⇒Y) } --_≅_.from (e X⇒Y)
            ; commute = λ { {X₁ , X₂} {Y₁ , Y₂} f → {!   !} }
            }
          ; F⇐G = ntHelper record
            { η = λ { (S , e) → _≅_.to (e X⇒Y) }
            ; commute = {!   !}
            }
          ; iso = λ { (S , e) → record
            { isoˡ = _≅_.isoˡ (e X⇒Y)
            ; isoʳ = _≅_.isoʳ (e X⇒Y)
            } }
          }
        }
      }
    ; ⊤-is-terminal = record
      { ! = λ {K} →
        let module K = Cone K
        in record
        { arr = record
          { F₀ = λ x → (λ j → Functor.F₀ (K.ψ j) x) , λ f → {! K.commute f  !}
          ; F₁ = {!   !}
          ; identity = {!   !}
          ; homomorphism = {!       !}
          ; F-resp-≈ = {!   !}
          }
        ; commute = {!   !}
        }
      ; !-unique = {!   !}
      } {-record
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
       --open import Categories.Morphism J

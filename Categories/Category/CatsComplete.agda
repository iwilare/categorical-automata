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
open import Categories.NaturalTransformation using (ntHelper; NaturalTransformation)
open NaturalTransformation
open import Categories.NaturalTransformation.NaturalIsomorphism -- using (ntHelper; NaturalIsomorphism)
open import Categories.Morphism
import Categories.Morphism.Reasoning as MR

import Categories.Category.Construction.Cones as Co

open Π using (_⟨$⟩_)

module Categories.Category.CatsComplete where

Cats-Complete : {o ℓ e o' ℓ' e' : Level} → Complete o ℓ e (Cats (o ⊔ ℓ) ((o ⊔ ℓ)) ((o ⊔ ℓ))) -- (suc (o ⊔ ℓ ⊔ e ⊔ ℓ')) (suc (o ⊔ ℓ ⊔ e ⊔ e'))) --(c ⊔ ℓ ⊔ o ⊔ ℓ′) (o ⊔ ℓ′))
Cats-Complete {o} {ℓ} {e} {o'} {ℓ'} {e'} {J = J} F =
  record
  { terminal = record
    { ⊤ = record
      { N = record
        { Obj = Σ (∀ (j : J.Obj) → Category.Obj (F.₀ j))
                  λ S → ∀ {X Y} (f : J [ X , Y ])
                      → (_≅_ (F.F₀ Y) (Functor.₀ (F.₁ f) (S X)) (S Y))
        ; _⇒_ = λ { (S₁ , e₁) (S₂ , e₂)
              → Σ (∀ (j : J.Obj) → Category._⇒_ (F.₀ j) (S₁ j) (S₂ j))
                  (λ A → ∀ {X Y} (X⇒Y : J [ X , Y ])
                       → let open Category (F.F₀ Y) in
                         (_≅_.from (e₂ X⇒Y) ∘ Functor.F₁ (F.F₁ X⇒Y) (A X) ≈ A Y ∘ _≅_.from (e₁ X⇒Y))
                       × (_≅_.to (e₂ X⇒Y) ∘ A Y ≈ Functor.F₁ (F.F₁ X⇒Y) (A X) ∘ _≅_.to (e₁ X⇒Y))) }
        ; _≈_ = λ { a b → ∀ (j : J.Obj)
                   → Category._≈_ (F.₀ j) (proj₁ a j) (proj₁ b j) }
        ; id = (λ j → Category.id (F.F₀ j)) , λ {X} {Y} X⇒Y →
                  let open Category (F.F₀ Y)
                      open HomReasoning
                      open MR (F.F₀ Y) in (elimʳ (Functor.identity (F.F₁ X⇒Y)) ○ Equiv.sym identityˡ)
                                        , (identityʳ ○ introˡ (Functor.identity (F.F₁ X⇒Y)))
        ; _∘_ = λ { (S₁ , e₁) (S₂ , e₂) → (λ j → Category._∘_ (F.₀ j) (S₁ j) (S₂ j)) , λ {X} {Y} X⇒Y →
                  let open Category (F.F₀ Y)
                      open HomReasoning
                      open MR (F.F₀ Y) in ((refl⟩∘⟨ Functor.homomorphism (F.F₁ X⇒Y)) ○ extendʳ (proj₁ (e₁ X⇒Y)) ○ (refl⟩∘⟨ proj₁ (e₂ X⇒Y)) ○ sym-assoc)
                                         , (sym-assoc ○ (proj₂ (e₁  X⇒Y) ⟩∘⟨refl ○ (pullʳ (proj₂ (e₂ X⇒Y)) ○ pullˡ (Equiv.sym (Functor.homomorphism (F.F₁ X⇒Y)))))) }
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
        ; ∘-resp-≈  = λ f≈g h≈d j → Category.∘-resp-≈ (F.₀ j) (f≈g j) (h≈d j)
        }
      ; apex = record
        { ψ = λ j → record
            { F₀ = λ (S , _) → S j
            ; F₁ = λ (f , _) → f j
            ; identity = Category.Equiv.refl (F.₀ j)
            ; homomorphism = Category.Equiv.refl (F.₀ j)
            ; F-resp-≈ = λ f≈g → f≈g j
            }
        ; commute = λ {X} {Y} X⇒Y → record
          { F⇒G = ntHelper record
            { η = λ { (S , e) → _≅_.from (e X⇒Y) }
            ; commute = λ { {S₁ , e₁} {S₂ , e₂} (e , g) → proj₁ (g X⇒Y) }
            }
          ; F⇐G = ntHelper record
            { η = λ { (S , e) → _≅_.to (e X⇒Y) }
            ; commute = λ { {S₁ , e₁} {S₂ , e₂} (e , g) → proj₂ (g X⇒Y) }
            }
          ; iso = λ { (S , e) → record
            { isoˡ = _≅_.isoˡ (e X⇒Y)
            ; isoʳ = _≅_.isoʳ (e X⇒Y)
            } }
          }
        }
      }
    ; ⊤-is-terminal =
      record
        { ! = λ {K} →
          let module K = Cone K
          in record
          { arr = record
            { F₀ = λ x → (λ j → Functor.F₀ (K.ψ j) x)
                 , λ f → record
                  { from = NaturalIsomorphism.⇒.η (K.commute f) x
                  ; to   = NaturalIsomorphism.⇐.η (K.commute f) x
                  ; iso  = record { isoˡ = Iso.isoˡ (NaturalIsomorphism.iso (K.commute f) x)
                                  ; isoʳ = Iso.isoʳ (NaturalIsomorphism.iso (K.commute f) x)
                                  }
                  }
            ; F₁ = λ f → (λ j → Functor.₁ (K.ψ j) f)
                , (λ {X} {Y} X⇒Y → commute (NaturalIsomorphism.F⇒G (K.commute X⇒Y)) f
                                 , commute (NaturalIsomorphism.F⇐G (K.commute X⇒Y)) f)
            ; identity = λ j → Functor.identity (K.ψ j)
            ; homomorphism =  λ j → Functor.homomorphism (K.ψ j)
            ; F-resp-≈ = λ f≈g j → Functor.F-resp-≈ (K.ψ j) f≈g
            }
          ; commute = λ {X} → record
            { F⇒G = ntHelper (record
              { η = λ _ → Category.id (F.F₀ X)
              ; commute = λ X⇒Y →
                let open Category (F.F₀ X)
                    open HomReasoning
                    open MR (F.F₀ X) in id-comm-sym
              })
            ; F⇐G = ntHelper (record
              { η = λ _ → Category.id (F.F₀ X)
              ; commute = λ X⇒Y →
                let open Category (F.F₀ X)
                    open HomReasoning
                    open MR (F.F₀ X) in id-comm-sym
              })
            ; iso = λ _ → record
              { isoˡ = Category.identity² (F.F₀ X)
              ; isoʳ = Category.identity² (F.F₀ X)
              }
            }
          }
        ; !-unique =
          λ {K} f →
            let module f = Cone⇒ f in record
            { F⇒G = ntHelper (record
              { η = λ X → (λ j → NaturalIsomorphism.⇐.η (Cone⇒.commute f) X)
                         , (λ {X} {Y} X⇒Y →
                             let open Category (F.F₀ Y)
                                 open HomReasoning in ( {! Equiv.sym (NaturalIsomorphism.⇐.commute f.commute ?) !}
                                                      ○ {!   Equiv.sym (NaturalIsomorphism.iso.isoʳ f.commute ?) !}) -- NaturalIsomorphism.⇐.commute (f.commute ?)
                                                    , ({!   !} ○ {!   !})  )
              ; commute = λ g j → NaturalIsomorphism.⇐.commute (Cone⇒.commute f) g
              })
            ; F⇐G = {!   !}
            ; iso = {!   !}
            }
        }
    }
  }
  where module F = Functor F
        module J = Category J
        open Co F
       --open import Categories.Morphism J
{-record
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

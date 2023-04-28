module Set.Utils where

open import Level using (suc)
open import Relation.Binary.PropositionalEquality using (_≡_)

record _≅_ {ℓ} (A B : Set ℓ) : Set (suc ℓ) where
  field
    to : A → B
    from : B → A
    to∘from=1 : ∀ x → (to (from x)) ≡ x
    from∘to=1 : ∀ x → (from (to x)) ≡ x

infix 15 _≅_

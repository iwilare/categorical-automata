module Set.Deaf where

open import Data.Product using (map₂; _,_; _×_)
open import Data.List using ([])
open import Data.Unit using (⊤)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

open import Set.Automata
open import Set.Functors

private
  variable
    I O A B C : Set

Deaf : Mealy A B → Set
Deaf M = ∀ {i} {i'} {e} → M.s (i , e) ≡ M.s (i' , e)
   where module M = Mealy M

deaf-mealified : {M : Mealy B C} {N : Moore A B}
  → Deaf (mealify N)
deaf-mealified = refl

∘-deaf-mealifiedₗ : {M : Mealy A B} {N : Moore B C}
  → Deaf (mealify N ⋄ M)
∘-deaf-mealifiedₗ = refl

∘-deaf-mealifiedᵣ : {M : Mealy B C} {N : Moore A B}
  → Deaf (M ⋄ mealify N)
∘-deaf-mealifiedᵣ = refl

∘-absorbDeafᵣ : {M : Mealy B C} {N : Mealy A B}
  → Deaf N
  → Deaf (M ⋄ N)
∘-absorbDeafᵣ {M = M} isDeaf = cong (λ p → Mealy.s M (p , _)) isDeaf

-- Deaf Mealy machines
record DMealy (I : Set) (O : Set) : Set₁ where
  field
    M : Mealy I O
    isDeaf : Deaf M

open import Set.LimitAutomata

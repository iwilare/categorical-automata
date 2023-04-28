module Set.Soft where

open import Data.Product using (map₂; _,_; _×_)
open import Data.List using ([])
open import Data.Unit using (⊤)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Set.Automata

private
  variable
    I O A B C : Set

Soft : Moore A B → Set
Soft M = ∀ {i} {s} → M.s (M.d (i , s)) ≡ M.s s
  where module M = Moore M

-- Soft Moore machines
record SMoore (I : Set) (O : Set) : Set₁ where
  field
    M : Moore I O
    isSoft : Soft M


{-
       ┌─────────────┐   ┌─────────────┐
       │             │   │  Soft      │
 ─ A ──┼─────────────┼─B─┼─────────────┼── C ───  is Soft
       │             │   │             │
       │  Mealy M    │   │ Moore N     │
       └─────────────┘   └─────────────┘
-}
∘-absorbSoft : {M : Mealy A B} {N : Moore B C}
  → Soft N
  → Soft (N ⋉ M)
∘-absorbSoft {M = M} isSoft = isSoft
  where module M = Mealy M

open import Set.LimitAutomata

Soft-P∞ : ∀ A → Soft (P∞ A)
Soft-P∞ A = refl

Soft-P∞⋉M : {M : Mealy A B} → Soft (P∞ B ⋉ M)
Soft-P∞⋉M {B = B} {i = i} {s = (a , b)} = Soft-P∞ B {i = P∞carrier.f b []} {s = b}

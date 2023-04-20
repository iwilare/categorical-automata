module Set.Acephalous where

open import Data.Product using (map₂; _,_; _×_)
open import Data.List using ([])
open import Data.Unit using (⊤)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Set.Automata

private
  variable
    I O A B C : Set

Acephalous : Moore A B → Set
Acephalous M = ∀ {i} {s} → M.s (M.d (i , s)) ≡ M.s s
  where module M = Moore M

-- Acephalous Moore machines
record AMoore (I : Set) (O : Set) : Set₁ where
  field
    M : Moore I O
    isAcephalous : Acephalous M


{-
       ┌─────────────┐   ┌─────────────┐
       │             │   │  aceph      │
 ─ A ──┼─────────────┼─B─┼─────────────┼── C ───  is aceph
       │             │   │             │
       │  Mealy M    │   │ Moore N     │
       └─────────────┘   └─────────────┘
-}
∘-absorbAceph : {M : Mealy A B} {N : Moore B C}
  → Acephalous N
  → Acephalous (N ⋉ M)
∘-absorbAceph {M = M} isAceph = isAceph
  where module M = Mealy M

open import Set.LimitAutomata

acephalous-P∞ : ∀ A → Acephalous (P∞ A)
acephalous-P∞ A = refl

acephalous-P∞⋉M : {M : Mealy A B} → Acephalous (P∞ B ⋉ M)
acephalous-P∞⋉M {B = B} {i = i} {s = (a , b)} = acephalous-P∞ B {i = P∞carrier.f b []} {s = b}

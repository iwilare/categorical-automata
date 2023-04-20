module Set.LimitAutomata where

open import Data.Product using (_,_; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Data.List.NonEmpty using (List⁺; _∷⁺_; toList; [_])
open import Data.List using (List; [];  _∷_)
open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)

open import Set.Automata

private
  variable
    I O A B C : Set

-- terminal object of Mealy
TerminalMealy : ∀ I O → Mealy I O
TerminalMealy I O = record
  { E = List⁺ I → O
  ; d = λ { (i , f) xs → f (i ∷⁺ xs) }
  ; s = λ { (a , f) → f [ a ] }
  }

-- terminal object of Moore
TerminalMoore : ∀ I O → Moore I O
TerminalMoore I O = record
  { E = List I → O
  ; d = λ { (i , f) xs → f (i ∷ xs) }
  ; s = λ { f → f [] }
  }

-------------------------------------------------------------------------------

-- Terminal acephalous Moore machine: subobject of the terminal
-- object only considering functions on lists that ignore the first element
{-
   P∞ ───┬────────────►  1
   │     │               │
   ├─────┘               │
   │                     │ head
   │                     │
   ▼                     ▼
[A*,A] ──────────────► [A+,A]
           [i,A]
-}
record P∞carrier (A : Set) : Set where
  field
    f : List A → A
    eq : ∀ (t : List⁺ A) → f (toList t) ≡ List⁺.head t

P∞ : ∀ A → Moore A A
P∞ A = record
  { E = P∞carrier A
  ; d = λ { (_ , e) → e }
  ; s = λ x → P∞carrier.f x []
  }

module P∞ A = Moore (P∞ A)

-------------------------------------------------------------------------------

-- The Queue machine: save each input as set
-- of states and immediately output it as is
Queue : Moore A A
Queue {A} = record
  { E = A
  ; d = λ { (i , _) → i }
  ; s = λ x → x
  }

-- The Queueₙ machines: save each output in the states, keeping
-- a queue of things to output. When `d` is called, add an element to the
-- queue and pop the last one.

Queue₂ : Moore A A
Queue₂ {A} = record
  { E = A × A
  ; d = λ { (i , (a , b)) → (i , a) }
  ; s = λ (a , b) → b
  }

Queue₃ : Moore A A
Queue₃ {A} = record
  { E = A × A × A
  ; d = λ { (i , (a , b , c)) → (i , a , b) }
  ; s = λ (a , b , c) → c
  }

Queue₄ : Moore A A
Queue₄ {A} = record
  { E = A × A × A × A
  -- Pop the head, push at the bottom, shift the rest
  ; d = λ { (i , (a , b , c , d)) → (i , a , b , c) }
  -- Output the head of the queue
  ; s = λ (a , b , c , d) → d
  }

Queueₙ : ℕ → Moore A A
Queueₙ {A} n = record
  -- Successor because we must have at least one element
  -- to be able to define output
  { E = Fin (ℕ.suc n) → A
  -- Pop the head, push at the bottom, shift the rest
  ; d = λ { (i , v) Fin.zero → i
          ; (i , v) (Fin.suc n) → v (Fin.suc n) }
  -- Output the head of the queue
  ; s = λ x → x (Data.Fin.fromℕ n)
  }

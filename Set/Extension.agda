
module Set.Extension where

open import Data.Product using (_,_; _×_; map₁; map₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.List.NonEmpty using (List⁺; _∷_; _∷⁺_; toList; [_]; last)
open import Data.List using (List; []; _∷_)
open import Function using (_∘_)

private
  variable
    I O A B C : Set

open import Set.Automata

-- extensions of Moore and Mealy machines

abstract
  extend : (I × A → A) → (List I × A → A)
  extend d (is , s) = extend-curried d is s
    where
      extend-curried : (I × A → A) → List I → A → A
      extend-curried d []       s = s
      extend-curried d (x ∷ xs) s = extend-curried d xs (d (x , s))

moore-ext : Moore A B → Mealy (List A) B
moore-ext {A} {B} M = let module M = Moore M in record
  { E = M.E
  ; d = extend M.d
  ; s = M.s ∘ extend M.d
  }

mealy-ext : Mealy A B → Mealy (List⁺ A) B
mealy-ext {A} {B} M = let module M = Mealy M in record
  { E = M.E
  ; d = extend M.d ∘ map₁ toList
  ; s = λ { (xs , s) → M.s (last xs , extend M.d (toList xs , s)) }
  }

moore-list⁺-inclusion : Moore (List A) B → Moore (List⁺ A) B
moore-list⁺-inclusion M = record
  { E = M.E
  ; d = M.d ∘ map₁ toList
  ; s = M.s
  } where module M = Moore M

moore-list⁺-ext : Moore (List⁺ A) B → Moore (List A) B
moore-list⁺-ext M = record
  { E = M.E
  ; d = λ { ([]    , s) → s
          ; (x ∷ i , s) → M.d (x ∷ i , s)
          }
  ; s = M.s
  } where module M = Moore M

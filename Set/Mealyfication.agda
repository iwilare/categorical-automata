module Set.Mealyfication where

open import Data.Product using (_,_; _×_; proj₁; proj₂; curry)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong₂; cong; trans; sym)
open import Data.List.NonEmpty using (List⁺; _∷_; _∷⁺_; toList; [_])
open import Data.List using (List; []; _∷_)
open import Function using (id; _∘_; flip)
open import Data.Nat using (ℕ)
open import Data.Fin using (Fin; zero; suc)
open import Data.Vec using (Vec; head; _∷ʳ_; _∷_; foldl; replicate)

open import Set.Automata
open import Set.LimitAutomata
open import Set.Soft
open import Set.Equality
open import Set.Extension
open import Set.Functors
open import Set.Utils

private
  variable
    I O A B C : Set
    Mre : Moore A B
    Mly : Mealy A B

J⋄ : {Mly : Mealy A B} {Mre : Moore B C}
   → mealify Mre ⋄ Mly ≡ mealify (Mre ⋉ Mly)
J⋄ = refl

⋄J : {Mly : Mealy B C} {Mre : Moore A B}
   → Mly ⋄ mealify Mre ≡ mealify (Mly ⋊ Mre)
⋄J = refl

J⋊ : {Mre : Moore B C} {Mre' : Moore A B}
   → mealify Mre ⋊ Mre' ≡ Mre ⋉ mealify Mre'
J⋊ = refl

J⋄J : {Mre : Moore B C} {Mre' : Moore A B}
   → mealify (Mre ⋈ Mre') ≡ mealify Mre ⋄ mealify Mre'
J⋄J = refl

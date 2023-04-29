module Set.Functors where

open import Data.Product using (_,_; _×_; proj₁; proj₂; curry; map₂; map₁; swap)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong₂; cong; trans; sym)
open import Data.List.NonEmpty using (List⁺; _∷_; _∷⁺_; toList; [_]; last; snocView; _∷ʳ′_)
open import Data.List using (List; []; _∷_)
open import Function using (id; _∘_; flip)
open import Data.Nat using (ℕ)
open import Data.Fin using (Fin; zero; suc)
open import Data.Vec using (Vec; head; _∷ʳ_; _∷_; foldl; replicate)

open import Set.Automata
open import Set.LimitAutomata
open import Set.Soft
open import Set.Utils
open import Set.Equality

private
  variable
    I O A B C : Set
    Mre : Moore A B
    Mly : Mealy A B

mealify : Moore A B → Mealy A B
mealify M = record
  { E = M.E
  ; d = M.d
  ; s = M.s ∘ proj₂
  } where module M = Moore M

mealify-advance : Moore A B → Mealy A B
mealify-advance M = record
  { E = M.E
  ; d = M.d
  ; s = λ { (i , s) → M.s (M.d (i , s)) }
  } where module M = Moore M

mealify-advance₂ : Moore A B → Mealy A B
mealify-advance₂ {A} {B} M = let module M = Moore M in record
  { E = A × M.E
  ; d = λ {(a , a' , e) → a , M.d (a' , e)}
  ; s = λ {(a , a' , e) → M.s (M.d (a , M.d (a' , e)))}
  }

moorify : Mealy A B → Moore A B
moorify = Queue ⋉_

moorify-pre : Mealy A B → Moore A B
moorify-pre = _⋊ Queue

𝕂 : Mealy A B → SMoore A B
𝕂 M = record
  { M = P∞ _ ⋉ M
  ; isSoft = refl
  }

module ExtensionFunctors where

  -- extensions of Moore and Mealy machines

  abstract
    extend : (I × A → A) → (List I × A → A)
    extend d (is , s) = extend-curried d is s
      where
        extend-curried : (I × A → A) → List I → A → A
        extend-curried d []       s = s
        extend-curried d (x ∷ xs) s = extend-curried d xs (d (x , s))

    extend-nil : ∀ {f : I × A → A} {e : A} → extend f ([] , e) ≡ e
    extend-nil = refl

  moore-ext : Moore A B → Mealy (List A) B
  moore-ext {A} {B} M = let module M = Moore M in record
    { E = M.E
    ; d = extend M.d
    ; s = M.s ∘ extend M.d
    }

  mealy-ext : Mealy A B → Mealy (List⁺ A) B
  mealy-ext {A} {B} M = record
    { E = M.E
    ; d = extend M.d ∘ map₁ toList
    ; s = λ { (xs , s) → M.s (last xs , extend M.d (toList xs , s)) }
    } where
      module M = Mealy M

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

open ExtensionFunctors public

e𝕁 : Moore A B → Mealy (List⁺ A) B
e𝕁 M = mealy-ext (mealify-advance M)

𝕁𝕃e : Moore A B → Mealy (List⁺ A) B
𝕁𝕃e M = mealify-advance (moore-list⁺-inclusion (moorify (moore-ext M)))

-- Lemma: extending and converting a Moore machine is the same as
-- first converting to Mealy machine and then extend it as Mealy.
extend-convert-moore : ∀ {Mre : Moore A B}
  → Mealy[ toList , id ] (moore-ext Mre) ≡ mealy-ext (mealify Mre)
extend-convert-moore {Mre = Mre} = refl

module Fleshouts where
  _ : (let module Mly = Mealy Mly)
    → Mly ⋊ Queue ≡
    record { E =  A × Mealy.E Mly
          ; d = λ { (a , a' , e) → a , (Mly.d (a' , e))}
          ; s = λ { (a , e) → Mly.s (a , e)}
          }
  _ = refl

  _ : (let module Mly = Mealy Mly)
    → Mly ⋊ P∞ _ ≡
    record { E =  P∞carrier _ × Mly.E
          ; d = λ {(a , f , e) → f , Mly.d (P∞carrier.f f [] , e)}
          ; s = λ {(f , e) → Mly.s (P∞carrier.f f [] , e)}
          }
  _ = refl

  _ : (let module Mly = Mealy Mly)
    → moorify Mly ≡
    record { E = Mealy.E Mly × B
           ; d = λ { (a , e , b) → Mly.d (a , e) , Mly.s (a , e)}
           ; s = λ {(e , b) → b}
           }
  _ = refl

  _ : (let module Mly = Mealy Mly)
    → P∞ _ ⋉ Mly ≡
    record { E =  Mealy.E Mly × P∞carrier _
          ; d = λ { (a , e , f) → Mly.d (a , e) , f }
          -- dᵢ : Eᵢ x A --> Eᵢ : colim(dᵢ) = colim(Eᵢ) x A = colim (Eᵢ x A) --~-> colim(Eᵢ)
          ; s = λ { (e , f) → P∞carrier.f f [] }
          }
  _ = refl

  _ : (let module Mly = Mealy Mly)
    → ((Queue ⋈_) ∘ moorify) Mly ≡
    record { E = ((Mealy.E Mly) × B) × B
          ; d = λ { (a , (e , b) , e') → (Mly.d (a , e) , Mly.s (a , e)) , b  }
          ; s = λ { (e , b) → b }
          }
  _ = refl

  _ : (let module Mre = Moore Mre)
    → (mealy-ext ∘ mealify-advance) Mre ≡ record
    { E = Moore.E Mre
    ; d = λ { (l , e) → extend (Moore.d Mre) (toList l , e) }
    ; s = λ { (h ∷ tail , e) → Moore.s Mre (Moore.d Mre  (Data.List.NonEmpty.last (h ∷ tail) ,   extend (Mealy.d (mealify-advance Mre)) (toList (h ∷ tail) , e))) }
    }
  _ = refl

  _ : (let module Mre = Moore Mre)
    → (Mealy[ toList , id ] ∘ moore-ext) Mre ≡ record
    { E = Moore.E Mre
    ; d = λ { (a , e) → extend Mre.d (toList a , e) }
    ; s = λ { (a , e) → Mre.s (extend Mre.d (toList a , e)) }
    }
  _ = refl

  {-
  _ : (let module Mly = Mealy Mly)
    → (moore-list⁺-ext ∘ moorify ∘ mealy-ext) Mly ≡
    record { E = (Mealy.E Mly) × B
          ; d = λ { (fst , fst₁ , snd) → {!   !} }
          ; s = λ { (e , e') → e' } }
  _ = refl

  _ : (let module Mly = Mealy Mly)
    → (moorify ∘ moore-ext ∘ moorify) Mly ≡
    record { E = ((Mealy.E Mly) × B) × B
          ; d = λ { (a , (e , b) , e') → {!  !} }
          ; s = λ { (e , e') → e' } }
  _ = refl
  -}

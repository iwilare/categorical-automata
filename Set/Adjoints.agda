module Set.Adjoints where

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
open import Set.Utils
open import Set.Equality
open import Set.Extension

private
  variable
    I O A B C : Set
    Mre : Moore A B
    Mly : Mealy A B

module Functors where

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

  e𝕁 : (M : Moore A B) → Mealy (List⁺ A) B
  e𝕁 M = mealy-ext (mealify-advance M)

  𝕁𝕃e : (M : Moore A B) → Mealy (List⁺ A) B
  𝕁𝕃e M = mealify-advance (moore-list⁺-inclusion (moorify (moore-ext M)))

open Functors

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

module Adjunctions where

  𝕁⊣𝕃 : (M : Moore A B) → (N : Mealy A B) → (Mealy⇒ (mealify-advance M) N) ≅ (Moore⇒ M (moorify N))
  𝕁⊣𝕃 M N = let module M = Moore M
                module N = Mealy N in record
    { to = λ α → let module α = Mealy⇒ α in record
      { hom = λ x → (α.hom x) , (M.s x)
      ; d-eq = λ {(a , e) → cong₂ _,_ (α.d-eq (a , e)) (sym (α.s-eq (a , e)))}
      ; s-eq = λ x → refl
      }
    ; from = λ β → let module β = Moore⇒ β in record
      { hom = λ x → proj₁ (β.hom x)
      ; d-eq = λ {(a , e) → cong proj₁ (β.d-eq (a , e))}
      ; s-eq = λ {(a , e) → trans (sym (cong proj₂ (β.d-eq (a , e)))) (β.s-eq (β.X.d (a , e)))}
      }
    ; to∘from=1 = λ x → let module x = Moore⇒ x
                          in Moore⇒-≡ _ x (extensionality (λ t → sym (cong (λ b → proj₁ (x.hom t) , b) (x.s-eq t))))
    ; from∘to=1 = λ x → Mealy⇒-≡ _ x refl
    }

  {-
  𝕁⊣𝕃' : (M : Moore A B) → (N : Mealy A B) →  (Mealy⇒ N ({!   !} M)) ≅ (Moore⇒ (moorify N) M)
  𝕁⊣𝕃' M N = let module M = Moore M
                 module N = Mealy N in record
    { to = λ α → let module α = Mealy⇒ α in record
      { hom  = λ { m → {!   !} } -- α.hom x , M.s x
      ; d-eq = λ { g → {!   !} } --(a , e) → cong₂ _,_ (α.d-eq _) {! sym (α.s-eq (a , e))  !} } --λ {(a , e) → cong₂ _,_ (α.d-eq (a , e)) (sym (α.s-eq (a , e)))}
      ; s-eq = {!   !} --λ x → refl
      }
    ; from = λ β → let module β = Moore⇒ β in record
      { hom  = λ n → {!   !} --proj₁ ∘ β.hom --λ x → proj₁ (β.hom x)
      ; d-eq = {!   !} --λ {(a , e) → cong proj₁ (β.d-eq (a , e))}
      ; s-eq = {!   !} --λ {(a , e) → trans (sym (cong proj₂ (β.d-eq (a , e)))) (β.s-eq (β.X.d (a , e)))}
      }
    ; to∘from=1 = λ x → let module x = Moore⇒ x
                         in Moore⇒-≡ _ x {!   !} --λ x → let module x = Moore⇒ x
                    --        in Moore⇒-≡ _ x (extensionality (λ t → sym (cong (λ b → proj₁ (x.hom t) , b) (x.s-eq t))))
    ; from∘to=1 = λ x → Mealy⇒-≡ _ x {!   !}
    }
    -}

  module AdjunctionsExperiments where

    i⊣𝕂 : (M : Moore A B) → (soft : Soft M) → (N : Moore A B) → (Moore⇒ M N) ≅ (Moore⇒ M (P∞ _ ⋈ N))
    i⊣𝕂 M soft N = let module M = Moore M
                       module N = Moore N in record
      { to = λ α → let module α = Moore⇒ α in record { hom = λ x → (α.hom x) , (homP∞ (α.X.s x))
        ; d-eq = λ {(a , e) → cong₂ _,_ (α.d-eq (a , e)) (cong homP∞ (soft))}
        ; s-eq = λ {e → refl} }
      ; from = λ β → let module β = Moore⇒ β in record { hom = λ x → proj₁ (β.hom x)
        ; d-eq = λ {(a , e) → cong proj₁ (β.d-eq (a , e)) }
        ; s-eq = λ {e → trans {!   !} (β.s-eq e) } }
      ; to∘from=1 = λ {x → let module x = Moore⇒ x in
                    Moore⇒-≡ _ x (extensionality λ t
                                    → cong (λ v → (proj₁ (x.hom t) , v))
                                          (P∞-≡ (homP∞ (x.X.s t))
                                                  (proj₂ (x.hom t))
                                                  (extensionality (λ { [] → sym (x.s-eq t)
                                                                      ; (x ∷ w) → sym (P∞carrier.eq (proj₂ (x.hom t)) (x ∷ w))
                                                                      }))))}
      ; from∘to=1 = λ x → Moore⇒-≡ _ x refl
      } where
          homP∞ : B → (P∞carrier B)
          homP∞ b = record
            { f = λ { [] → b
                    ; (x ∷ tail) → x}
            ; eq = λ t → refl
            }

    KL≅L' : (M : Mealy A B) → (Moore.E (P∞ _ ⋈ (moorify M))) ≅ (Moore.E (P∞ _ ⋉ M))
    KL≅L' M = let module M = Mealy M in record
      { to = λ {((e , b) , f) → e , f}
      ; from = λ {(e , f) → (e , P∞carrier.f f []) , f}
      ; to∘from=1 = λ {(fst , snd) → refl} -- can be done
      ; from∘to=1 = λ {((a , b) , snd) → cong₂ _,_  (cong₂ _,_ refl {!   !}) refl} -- can be done?
      }

------------------------- experiments ---------------------------------------------------------------------------------------------

equ : (Moore (List A) B) ≅ (Moore (List⁺ A) B)
equ = record {
    to = moore-list⁺-inclusion
  ; from = moore-list⁺-ext
  ; to∘from=1 = λ { record { E = E ; d = d ; s = s } → {!   !}  }
  ; from∘to=1 = λ { record { E = E ; d = d ; s = s } → {!   !} }
  }

-- if Ji -| moorify', then P∞ _ ⋉ ≅ KL:
-- Ji x -> y
-- ix -> 𝕃y
-- x -> KLy => KL ≅ L'

{-
mealify-advance₂⊣𝕃² : (M : Moore A B) → (N : Mealy A B) → (Mealy⇒ (mealify-advance₂ M) N) ≅ (Moore⇒ M (Queue ⋈ (moorify N)))
mealify-advance₂⊣𝕃² M N = let module M = Moore M
                              module N = Mealy N in
  record { to = λ α → let module α = Mealy⇒ α in
            record { hom = λ {x → ({! α.hom   !} , {!   !}) , {!   !}}
                   ; d-eq = λ {(a , e) → {!  α.s-eq (a , e) !}}
                   ; s-eq = λ x → refl }
         ; from = λ β → let module β = Moore⇒ β in
            record { hom = λ x → {!   !}
                   ; d-eq = λ {(a , e) → {!   !}}
                   ; s-eq = λ {(a , e) → {!   !}} }
         ; to∘from=1 = λ x → let module x = Moore⇒ x in Moore⇒-≡ _ x {!   !}
         ; from∘to=1 = λ x → Mealy⇒-≡ _ x {!   !}
         }

-- can't commute: the number of times one applies moorify must be the same.
-- but:

morphism? : (M : Mealy A B) → Moore⇒ ((moorify ∘ moore-ext ∘ moorify) M)
                                      ((moore-list⁺-ext ∘ moorify ∘ mealy-ext) M)
morphism? M = record
  { hom = λ {((e , b) , b') → e , b'}
  ; d-eq = λ {(e , (e' , b) , b') → cong₂ _,_ {!   !} {!   !}}
  ; s-eq = λ {((e , b') , b) → refl}
  }

quadrato : ∀ {M : Moore A B} → Mealy[ toList , id ] (moore-ext M) ≡ mealy-ext (mealify-advance M)
quadrato {M = record { E = E ; d = d ; s = s }} = {!   !}

morphism2? : (M : Moore A B) → Mealy⇒ (e𝕁 M) (𝕁𝕃e M)
morphism2? M = let module M = Moore M in record
  { hom = λ x → x , M.s x
  ; d-eq = λ {(a ∷ [] , e) → refl
            ; (a ∷ x ∷ as , e) → {!   !} } --cong₂ _,_ (cong (λ t → M.d (a , t)) (cong (λ p → M.d (x , p)) {!   !})) (cong (λ t → M.s (M.d (a , t))) {!   !})}
  ; s-eq = λ {(a ∷ as , e) → {!   !}}
  }

  mealify-advanceₙ : ℕ → Moore A B → Mealy A B
  mealify-advanceₙ {A} {B} n M = record
    { E = Vec B n × M.E
    ; d = λ { (a , f) → {!   !} }
    ; s = λ { (a , g) → M.s {!   !} }
    } where module M = Moore M
            d = flip (curry M.d)

  aggiunzia-divina : ∀ {n}
    → (Mealy⇒ (mealify-advanceₙ n Mre) Mly) ≅ (Moore⇒ Mre (Queueₙ n ⋉ Mly))
  aggiunzia-divina {Mre = Mre} {Mly = Mly} = record
      { to = λ α → let module α = Mealy⇒ α in record
        { hom = λ x → α.hom (replicate (Mre.s x) , x) , replicate (Mre.s x) --α.hom {! Mly.s  !} , replicate (Mre.s x) --λ s → (α.hom (s , {!   !})) , replicate (Mre.s s)
        ; d-eq = {!   !}
        ; s-eq = {!   !}
        }
      ; from = λ α → let module α = Moore⇒ α in record
        { hom = λ f → proj₁ (α.hom (proj₂ f)) --proj₁ (α.hom {! Mre.s  !}) --proj₁ (α.hom (f {! Mre.s  !})) --λ { (s , v) → proj₁ (α.hom s) }
        ; d-eq = {!   !}
        ; s-eq = {!   !}
        }
      ; to∘from=1 = λ x → let module x = Moore⇒ x in
          Moore⇒-≡ _ x (extensionality λ x → {! x.s-eq x  !})
      ; from∘to=1 = λ x → let module x = Mealy⇒ x in
          Mealy⇒-≡ _ x ((extensionality λ x → {! x.d-eq  !}))
      }
    where module Mre = Moore Mre
          module Mly = Mealy Mly

  aggiunzia-divina-reverse : ∀ {n}
    → (Mealy⇒ Mly (mealify-advanceₙ n Mre)) ≅ (Moore⇒ (Queueₙ n ⋉ Mly) Mre)
  aggiunzia-divina-reverse {Mly = Mly} {Mre = Mre} = record
      { to = λ α → let module α = Mealy⇒ α in record
        { hom = {!   !} --λ { (s , x ∷ v) → {! α.hom  !} } --α.hom s {! Mre.s  !} } -- λ s → (α.hom (s , {!   !})) , replicate (Mre.s s)
        ; d-eq = {!   !}
        ; s-eq = {!   !}
        }
      ; from = λ α → let module α = Moore⇒ α in record
        { hom = λ x → {!   !} --replicate (α.hom (x , {! Mre.s  !})) --λ v → α.hom (x , {! Mre.s  !}) --α.hom (x , replicate (Mre.s (Mre.d ({! Mly.d  !} , α.hom {!   !})))) , {!   !} --λ { (s , v) → proj₁ (α.hom s) }
        ; d-eq = {!   !}
        ; s-eq = {!   !}
        }
      ; to∘from=1 = λ x → let module x = Moore⇒ x in
          Moore⇒-≡ _ x (extensionality λ x → {! x.d-eq ?  !})
      ; from∘to=1 = {!   !}
      }
    where module Mre = Moore Mre
          module Mly = Mealy Mly
-}

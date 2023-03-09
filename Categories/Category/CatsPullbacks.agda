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
open import Categories.Category.Instance.StrictCats
open import Categories.Category.Complete
open import Categories.NaturalTransformation using (ntHelper; NaturalTransformation)
open NaturalTransformation
--open import Categories.NaturalTransformation.NaturalIsomorphism -- using (ntHelper; NaturalIsomorphism)
open import Categories.Morphism
import Categories.Morphism.Reasoning as MR
import  Categories.Morphism.HeterogeneousIdentity
import Categories.Category.Construction.Cones as Co

open import Categories.Diagram.Pullback

open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym)

open Π using (_⟨$⟩_)

module Categories.Category.CatsPullbacks where



Cats-Pullback-Cat : {o ℓ e o' ℓ' e' : Level}
       → {A B E : Category o ℓ e} (F : Functor A E) (G : Functor B E)
       → Category o (e ⊔ ℓ) e
Cats-Pullback-Cat {o} {ℓ} {e} {o'} {ℓ'} {e'} {A} {B} {E} F G =
 let module A = Category A
     module B = Category B
     module E = Category E
     module F = Functor F
     module G = Functor G
     open E.HomReasoning
     open MR E
     open Categories.Morphism.HeterogeneousIdentity E
     in record
  { Obj = Σ (A.Obj × B.Obj) (λ { (a , b) → G.₀ b ≡ F.₀ a })
  ; _⇒_ = λ { ((a , b) , p) ((a' , b') , p')
        → Σ (Category._⇒_ A a a' × Category._⇒_ B b b')
            (λ { (f , g) → F.₁ f E.∘ hid p E.≈ hid p' E.∘ G.₁ g }) }
  ; _≈_ = λ { ((f , f') , e) ((g , g') , e') → f A.≈ g × f' B.≈ g' }
  ; id = λ { {((a , b) , q)} → (A.id , B.id)
      , (elimˡ F.identity ○ introʳ G.identity) }
  ; _∘_ = λ { {(A1 , B1) , e1} {(A2 , B2) , e2} {(A3 , B3) , e3} ((f , f') , e) ((g , g') , e')
        → ((f A.∘ g) , (f' B.∘ g'))
         , (begin _ ≈⟨ (F.homomorphism ⟩∘⟨refl) ⟩
                  _ ≈⟨ ((refl⟩∘⟨ introʳ (hid-symʳ e1)) ⟩∘⟨refl) ⟩
                  _ ≈⟨ ((refl⟩∘⟨ pullˡ e') ⟩∘⟨refl) ⟩
                  _ ≈⟨ (pullˡ (pullˡ e) ⟩∘⟨refl) ⟩
                  _ ≈⟨ pullʳ (hid-symˡ e1) ⟩
                  _ ≈⟨ pullʳ E.identityʳ ⟩
                  _ ≈⟨ pullʳ (E.Equiv.sym G.homomorphism) ⟩
                  _ ∎)
         }
  ; assoc = A.assoc , B.assoc
  ; sym-assoc = A.sym-assoc , B.sym-assoc
  ; identityˡ = A.identityˡ , B.identityˡ
  ; identityʳ = A.identityʳ , B.identityʳ
  ; identity² = A.identity² , B.identity²
  ; equiv = record
    { refl = A.Equiv.refl , B.Equiv.refl
    ; sym = λ (f≈g₁ , f≈g₂) → A.Equiv.sym f≈g₁ , B.Equiv.sym f≈g₂
    ; trans = λ (f≈g₁ , f≈g₂) (g≈h₁ , g≈h₂)
            → A.Equiv.trans f≈g₁ g≈h₁ , B.Equiv.trans f≈g₂ g≈h₂
    }
  ; ∘-resp-≈ = λ (f≈g₁ , f≈g₂) (h≈i₁ , h≈i₂)
             → A.∘-resp-≈ f≈g₁ h≈i₁
             , B.∘-resp-≈ f≈g₂ h≈i₂
  }

Cats-Pullback : {o ℓ e o' ℓ' e' : Level}
       → {A B E : Category o (ℓ ⊔ e) e} (F : Functor A E) (G : Functor B E)
       → Pullback (StrictCats o (ℓ ⊔ e) e) F G --Pullback f g
Cats-Pullback {o} {ℓ} {e} {o'} {ℓ'} {e'} {A} {B} {E}  F G =
 let module A = Category A
     module B = Category B
     module E = Category E
     module F = Functor F
     module G = Functor G
     open E.HomReasoning
     open MR E
     open Categories.Morphism.HeterogeneousIdentity E
     in record
  { P = Cats-Pullback-Cat {A = A} {B = B} {E = E} F G
  ; p₁ = record
    { F₀ = λ { ((a , b) , e) → a }
    ; F₁ = λ { ((a , b) , e) → a }
    ; identity = A.Equiv.refl
    ; homomorphism = A.Equiv.refl
    ; F-resp-≈ = proj₁
    }
  ; p₂ = record
    { F₀ = λ { ((a , b) , e) → b }
    ; F₁ = λ { ((a , b) , e) → b }
    ; identity = B.Equiv.refl
    ; homomorphism = B.Equiv.refl
    ; F-resp-≈ = proj₂
    }
  ; isPullback = record
    { commute = record { eq₀ = λ ((a , b) , e) → sym e
                       ; eq₁ = λ { {(x , y) , p} {(z , w) , q} ((f , g) , e) →
                         begin _ ≈⟨ introʳ (hid-symʳ p) ○ E.assoc ⟩
                               _ ≈⟨ (refl⟩∘⟨ pullˡ e) ○ E.sym-assoc ⟩
                               _ ≈⟨ (pullˡ (hid-symˡ q) ⟩∘⟨refl) ⟩
                               _ ≈⟨ (E.identityˡ ⟩∘⟨refl) ⟩
                               _ ∎ }
                       }
    ; universal = λ { {h₁ = h₁} {h₂} (record { eq₀ = eq₀ ; eq₁ = eq₁ }) → record
      { F₀ = λ X → (Functor.₀ h₁ X , Functor.₀ h₂ X) , sym (eq₀ X)
      ; F₁ = λ {A} {B} f → (Functor.₁ h₁ f , Functor.₁ h₂ f) , 
                           (begin _ ≈⟨ introˡ (hid-symˡ (eq₀ B)) ⟩ 
                                  _ ≈⟨ center (eq₁ f) ⟩ 
                                  _ ≈⟨ (refl⟩∘⟨ pullʳ (hid-symʳ (eq₀ A))) ⟩ 
                                  _ ≈⟨ (refl⟩∘⟨ E.identityʳ) ⟩ 
                                  _ ∎)
      ; identity = Functor.identity h₁ , Functor.identity h₂
      ; homomorphism = Functor.homomorphism h₁ , Functor.homomorphism h₂
      ; F-resp-≈ = λ eq → Functor.F-resp-≈ h₁ eq , Functor.F-resp-≈ h₂ eq
      } }
    ; unique = λ { {eq = eq} p₁i≡h₁ p₂i≡h₂ → 
      record { eq₀ = λ X → {!  !} 
             ; eq₁ = λ f → {!   !} , {!   !} }}
    ; p₁∘universal≈h₁ = record 
      { eq₀ = λ X → {!   !} ; eq₁ = {!   !} }
    ; p₂∘universal≈h₂ = record 
      { eq₀ = λ X → {!   !} ; eq₁ = {!   !} }
    }
  }
 
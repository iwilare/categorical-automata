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
            (λ { (f , g) → F.₁ f E.≈ hid p' E.∘ G.₁ g E.∘ hid (sym p) }) }
  ; _≈_ = λ { ((f , f') , e) ((g , g') , e') → f A.≈ g × f' B.≈ g' }
  ; id = λ { {((a , b) , q)} → (A.id , B.id)
      , (F.identity ○ (E.Equiv.sym (hid-symʳ q) ○ (refl⟩∘⟨ introˡ G.identity))) }
  ; _∘_ = λ { {A , eA} {B , eB} {C , eC} ((f , f') , e) ((g , g') , e')
        → ((f A.∘ g) , (f' B.∘ g'))
         , (F.homomorphism ○ ((e ⟩∘⟨ e') ○ ((E.assoc ○ (refl⟩∘⟨ E.assoc)) ○ ((refl⟩∘⟨ refl⟩∘⟨ pullˡ (hid-symˡ eB)) ○ (refl⟩∘⟨ refl⟩∘⟨ E.identityˡ ○ (refl⟩∘⟨ pullˡ (E.Equiv.sym G.homomorphism))))))) } --({!   !} ○ (refl⟩∘⟨ {! Equiv.sym (pushʳ ?)  !}))) }
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
                       ; eq₁ = λ { ((f , g) , e) → (refl⟩∘⟨ e) ○ (pullˡ (hid-symˡ _) ○ E.identityˡ) }
                       }
    ; universal = λ { {h₁ = h₁} {h₂} (record { eq₀ = eq₀ ; eq₁ = eq₁ }) → record
      { F₀ = λ X → (Functor.₀ h₁ X , Functor.₀ h₂ X) , sym (eq₀ X)
      ; F₁ = λ f → (Functor.₁ h₁ f , Functor.₁ h₂ f) , hid-switch-sym {!   !} {!   !} {!   !} (eq₁ f ○ (refl⟩∘⟨ {!   !})) -- hid-switch (sym (eq₀ _)) _ _ {!   !} --sym (eq₀ X)
      ; identity = {!   !}
      ; homomorphism = {!   !}
      ; F-resp-≈ = {!   !}
      } }
    ; unique = {!   !}
    ; p₁∘universal≈h₁ = {!   !}
    ; p₂∘universal≈h₂ = {!   !}
    }
  }

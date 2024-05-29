{-# OPTIONS --allow-unsolved-metas #-}

open import Level
open import Data.Product using (Σ; proj₁; proj₂; _,_; Σ-syntax; _×_; -,_)
open import Function.Equality using (Π)
open import Relation.Binary using (Setoid; Rel)

open import Axiom.UniquenessOfIdentityProofs using (UIP)

open import Categories.Category using (Category; _[_,_])
open import Categories.Functor
open import Categories.Category.Instance.Setoids
open import Categories.Category.Instance.Properties.Setoids.Complete
open import Categories.Category.Instance.StrictCats
open import Categories.Category.Complete
open import Categories.NaturalTransformation using (ntHelper; NaturalTransformation)
open NaturalTransformation
--open import Categories.NaturalTransformation.NaturalIsomorphism -- using (ntHelper; NaturalIsomorphism)
open import Categories.Morphism
import Categories.Morphism.Reasoning as MR
import Categories.Morphism.HeterogeneousIdentity
import Categories.Category.Construction.Cones as Co

open import Categories.Functor.Equivalence

open import Categories.Diagram.Pullback

open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym)

open Π using (_⟨$⟩_)

module Categories.Category.StrictCatsPullbacks where

uip : ∀ {ℓ} {A : Set ℓ} → UIP A
uip refl refl = refl

Cats-Pullback-Cat : {o ℓ e : Level}
       → {A B E : Category o ℓ e} (F : Functor A E) (G : Functor B E)
       → Category o (e ⊔ ℓ) e
Cats-Pullback-Cat {o} {ℓ} {e} {A} {B} {E} F G =
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

Cats-Pullback : {o ℓ e : Level}
       → {A B E : Category o (ℓ ⊔ e) e} (F : Functor A E) (G : Functor B E)
       → Pullback (StrictCats o (ℓ ⊔ e) e) F G --Pullback f g
Cats-Pullback {o} {ℓ} {e} {A} {B} {E} F G =
  record
  { P = Cats-Pullback-Cat {o} {ℓ ⊔ e} {e} {A} {B} {E} F G
  ; p₁ = π₁
  ; p₂ = π₂
  ; isPullback = record
    { commute = record { eq₀ = λ ((a , b) , e) → sym e
                       ; eq₁ = λ { {(x , y) , p} {(z , w) , q} ((f , g) , e) →
                         begin _ ≈⟨ introʳ (hid-symʳ p) ○ E.assoc ⟩
                               _ ≈⟨ (refl⟩∘⟨ pullˡ e) ○ E.sym-assoc ⟩
                               _ ≈⟨ (pullˡ (hid-symˡ q) ⟩∘⟨refl) ⟩
                               _ ≈⟨ (E.identityˡ ⟩∘⟨refl) ⟩
                               _ ∎ }
                       }
    ; universal = universal
    ; unique =
        λ { {i = i} {eq = eq} p₁i≡h₁ p₂i≡h₂ →
          let module p₁i≡h₁ = Categories.Functor.Equivalence._≡F_ p₁i≡h₁ in
          let module p₂i≡h₂ = Categories.Functor.Equivalence._≡F_ p₂i≡h₂ in
          let module eq = Categories.Functor.Equivalence._≡F_ eq in
        record { eq₀ = unique₀ i eq p₁i≡h₁ p₂i≡h₂
                ; eq₁ = asdf i eq p₁i≡h₁ p₂i≡h₂ }  }
    ; p₁∘universal≈h₁ = record
      { eq₀ = λ X → refl ; eq₁ = λ _ → MR.id-comm-sym A }
    ; p₂∘universal≈h₂ = record
      { eq₀ = λ X → refl ; eq₁ = λ _ → MR.id-comm-sym B }
    }
  } where
    module A = Category A
    module B = Category B
    module E = Category E
    module F = Functor F
    module G = Functor G
    open E.HomReasoning
    open MR E
    open Categories.Morphism.HeterogeneousIdentity E

    π₁ : _
    π₁ = record
      { F₀ = λ { ((a , b) , e) → a }
      ; F₁ = λ { ((a , b) , e) → a }
      ; identity = A.Equiv.refl
      ; homomorphism = A.Equiv.refl
      ; F-resp-≈ = proj₁
      }
    π₂ : _
    π₂ = record
      { F₀ = λ { ((a , b) , e) → b }
      ; F₁ = λ { ((a , b) , e) → b }
      ; identity = B.Equiv.refl
      ; homomorphism = B.Equiv.refl
      ; F-resp-≈ = proj₂
      }

    universal : {A = A₁ : Category o (ℓ ⊔ e) e} {h₁ : Functor A₁ A}
      {h₂ : Functor A₁ B} →
      F ∘F h₁ ≡F G ∘F h₂ → Functor A₁ (Cats-Pullback-Cat {o} {ℓ ⊔ e} {e} {A} {B} {E} F G)
    universal {h₁ = h₁} {h₂} (record { eq₀ = eq₀ ; eq₁ = eq₁ }) = record
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
      }

    unique₀ : {Ai : Category o (ℓ ⊔ e) e}
        → {h₁ : Functor Ai A}
        → {h₂ : Functor Ai B}
        → (i : Functor Ai (Cats-Pullback-Cat {o} {ℓ ⊔ e} {e} {A} {B} {E} F G))
        → (let module i = Functor i)
        → (eq : F ∘F h₁ ≡F G ∘F h₂)
        → (p₂i≡h₂ : π₁ ∘F i ≡F h₁)
        → (p₁i≡h₁ : π₂ ∘F i ≡F h₂)
        → (X : Category.Obj Ai)
        → (let module eq = Categories.Functor.Equivalence._≡F_ eq)
        → Functor.F₀ i X ≡ (((Functor.F₀ h₁ X , Functor.F₀ h₂ X) , sym (eq.eq₀ X)))
    unique₀ i eq p₂i≡h₂ p₁i≡h₁ X with Functor.F₀ i X | _≡F_.eq₀ p₁i≡h₁ X | _≡F_.eq₀ p₂i≡h₂ X -- | {!   !} --uip ? ? --e (sym (_≡F_.eq₀ eq X))
    ... | ((a , b) , e) | refl | refl with uip e ((sym (_≡F_.eq₀ eq X)))
    ... | refl = refl

    asdf : {Ai : Category o (ℓ ⊔ e) e}
        → {h₁ : Functor Ai A}
        → {h₂ : Functor Ai B}
        → (i : Functor Ai (Cats-Pullback-Cat {o} {ℓ ⊔ e} {e} {A} {B} {E} F G))
        → (let module i = Functor i)
        → (eq : F ∘F h₁ ≡F G ∘F h₂)
        → (p₂i≡h₂ : π₁ ∘F i ≡F h₁)
        → (p₁i≡h₁ : π₂ ∘F i ≡F h₂)
        → (let module eq = Categories.Functor.Equivalence._≡F_ eq)
        → {X : Category.Obj Ai} {Y : Category.Obj Ai}
            (f : Ai [ X , Y ]) →
            Categories.Category.Definitions.CommutativeSquare
            (Cats-Pullback-Cat  {o} {ℓ ⊔ e} {e} {A} {B} {E} F G) (Functor.F₁ i f)
            (Categories.Morphism.HeterogeneousIdentity.hid
            (Cats-Pullback-Cat  {o} {ℓ ⊔ e} {e} {A} {B} {E} F G)
            (unique₀ i eq p₂i≡h₂ p₁i≡h₁ X))
            (Categories.Morphism.HeterogeneousIdentity.hid
            (Cats-Pullback-Cat  {o} {ℓ ⊔ e} {e} {A} {B} {E} F G)
            (unique₀ i eq p₂i≡h₂ p₁i≡h₁ Y))
            (Functor.F₁ (universal eq) f)
    asdf {Ai} {h₁} {h₂} i eq p₁i≡h₁ p₂i≡h₂ {X = X} {Y = Y} f with
              Functor.F₀ i Y | _≡F_.eq₀ p₂i≡h₂ Y | _≡F_.eq₀ p₁i≡h₁ Y
            | Functor.F₀ i X | _≡F_.eq₀ p₂i≡h₂ X | _≡F_.eq₀ p₁i≡h₁ X
            | Functor.F₁ i f
            | _≡F_.eq₁ p₁i≡h₁ f
            | _≡F_.eq₁ p₂i≡h₂ f
    ... | (.(Functor.F₀ h₁ Y) , .(Functor.F₀ h₂ Y)) , Gh₂Fh₁A | refl | refl
        | (.(Functor.F₀ h₁ X) , .(Functor.F₀ h₂ X)) , Gh₂Fh₁B | refl | refl
        | (h , h') , hs≈sh'
        | nice | supernice with uip Gh₂Fh₁A (sym (_≡F_.eq₀ eq Y)) | uip Gh₂Fh₁B (sym (_≡F_.eq₀ eq X))
    ... | refl | refl = nice , supernice

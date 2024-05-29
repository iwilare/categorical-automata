
module Set.Equality where

open import Level
open import Data.Product using (_,_; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.List.NonEmpty using (List⁺; _∷_; _∷⁺_; toList; [_])
open import Data.List using (List; []; _∷_)

open import Axiom.UniquenessOfIdentityProofs using (UIP)
open import Axiom.Extensionality.Propositional using (Extensionality)

private
  variable
    ℓ : Level
    I O A B C : Set ℓ

open import Set.Automata
open import Set.LimitAutomata

postulate
  extensionality : ∀ {ℓ ℓ′} → Extensionality ℓ ℓ′

uip : ∀ {ℓ} {A : Set ℓ} → UIP A
uip refl refl = refl

P∞-≡ : ∀ {A : Set} → (U : P∞carrier A) → (V : P∞carrier A) →
    P∞carrier.f U ≡ P∞carrier.f V → U ≡ V
P∞-≡ record { eq = eq₁ } record { eq = eq } refl with extensionality (λ x → uip (eq₁ x) (eq x))
... | refl = refl

Mealy⇒-≡ : ∀ {A B : Set} {M N : Mealy A B} (f g : Mealy⇒ M N) → Mealy⇒.hom f ≡ Mealy⇒.hom g → f ≡ g
Mealy⇒-≡ record { d-eq = d-eq₁ ; s-eq = s-eq₁ } record { d-eq = d-eq ; s-eq = s-eq } refl
  with extensionality (λ x → uip (d-eq₁ x) (d-eq x)) | extensionality (λ x → uip (s-eq₁ x) (s-eq x))
... | refl | refl = refl

Moore⇒-≡ : ∀ {A B : Set} {M N : Moore A B} (f g : Moore⇒ M N) → Moore⇒.hom f ≡ Moore⇒.hom g → f ≡ g
Moore⇒-≡ record { d-eq = d-eq₁ ; s-eq = s-eq₁ } record { d-eq = d-eq ; s-eq = s-eq } refl
  with extensionality (λ x → uip (d-eq₁ x) (d-eq x)) | extensionality (λ x → uip (s-eq₁ x) (s-eq x))
... | refl | refl = refl

Mealy-ext : ∀ {E I : Set} {s s′ : I × E → O} {d d′ : I × E → E}
          → (d-ext : ∀ i → d i ≡ d′ i)
          → (s-ext : ∀ i → s i ≡ s′ i)
          → (let p : Mealy I O
                 p = record { E = E ; d = d  ; s = s  }
                 q : Mealy I O
                 q = record { E = E ; d = d′ ; s = s′ } in p ≡ q)
Mealy-ext s-ext d-ext with extensionality s-ext | extensionality d-ext
... | refl | refl = refl

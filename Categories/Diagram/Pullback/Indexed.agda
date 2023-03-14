{-# OPTIONS --without-K --safe #-}

open import Categories.Category

-- this module characterizes a category of all Pullback indexed by I.
-- this notion formalizes a category with all Pullback up to certain cardinal.
module Categories.Diagram.Pullback.Indexed {o ℓ e} (C : Category o ℓ e) where

open import Level

open Category C

record IndexedPullbackOf {i} {I : Set i} {A : Obj} (O : I → Obj) (M : (i : I) → O i ⇒ A) : Set (i ⊔ o ⊔ e ⊔ ℓ) where
  field
    P   : Obj
    arr : ∀ i → P ⇒ O i

    -- a reference morphism
    ref : P ⇒ A
    equality  : ∀ i → M i ∘ arr i ≈ ref
    commute   : ∀ {X} (h : ∀ i → X ⇒ O i) (r : X ⇒ A) → (∀ i → M i ∘ h i ≈ r) → X ⇒ P
    universal : ∀ {X} (h : ∀ i → X ⇒ O i) (r : X ⇒ A) (eq : ∀ i → M i ∘ h i ≈ r) → ∀ i → h i ≈ arr i ∘ commute h r eq
    unique    : ∀ {X} {l : X ⇒ P} (h : ∀ i → X ⇒ O i) (r : X ⇒ A) (eq : ∀ i → M i ∘ h i ≈ r)
              → ∀ i
              → h i ≈ arr i ∘ l
              → l ≈ commute h r eq

record IndexedPullback {i} (I : Set i) : Set (i ⊔ o ⊔ e ⊔ ℓ) where
  field
    {A} : Obj
    O : I → Obj
    M : (i : I) → O i ⇒ A
    PullbackOf : IndexedPullbackOf O M

  open IndexedPullbackOf PullbackOf public

AllPullbacks : ∀ i → Set (o ⊔ ℓ ⊔ e ⊔ suc i)
AllPullbacks i = (I : Set i) → IndexedPullback I

AllPullbacksOf : ∀ i → Set (o ⊔ ℓ ⊔ e ⊔ suc i)
AllPullbacksOf i = ∀ {I : Set i} {A : Obj} (O : I → Obj) (M : (i : I) → O i ⇒ A) → IndexedPullbackOf O M

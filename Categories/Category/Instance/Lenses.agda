open import Data.Product using (Σ; Σ-syntax; proj₁; proj₂; _×_; _,_)
open import Level renaming (suc to lsuc)

open import Function.Inverse using (_↔_; Inverse; inverse) renaming (id to i-refl; sym to i-sym; _∘_ to i-fliptrans)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong-app)

open import Data.Unit.Polymorphic using (⊤; tt)

open import Categories.Category
open import Categories.Category.Monoidal
open import Categories.Comonad

open import Categories.Functor using (Functor) renaming (id to idF) using (_∘F_)
open import Categories.NaturalTransformation using (NaturalTransformation)

module Categories.Category.Instance.Lenses {o} where

private
  variable
    A B A′ B′ C : Set o
    X S Y R Z Q : Set o
    X′ S′ Y′ R′ : Set o

open import Relation.Binary.Definitions using (Trans)

i-trans : ∀ {f₁ f₂ m₁ m₂ t₁ t₂} →
      Trans (Inverse {f₁} {f₂} {m₁} {m₂})
            (Inverse {m₁} {m₂} {t₁} {t₂})
            (Inverse {f₁} {f₂} {t₁} {t₂})
i-trans = flip i-fliptrans
  where open import Function using (id; flip; _∘_)

open import Relation.Binary.Reasoning.Setoid
  (record { Carrier = Set o ; _≈_ = _↔_
          ; isEquivalence = record
            { refl = i-refl
            ; sym = i-sym
            ; trans = i-trans
            }
          })

module CategoryOfLens where

  open import Function using (id; flip; _∘_)

  record Lens (X S Y R : Set o) : Set (lsuc o) where
    field
      get : X → Y
      put : X × R → S

  Obj : Set (lsuc o)
  Obj = Set o × Set o

  _⇒_ : (X Y : Obj) → Set (lsuc o)
  (X , S) ⇒ (Y , R) = Lens X S Y R

  record _≈_ {A B} (L₁ L₂ : _⇒_ A B) : Set o where
    private
      module L₁ = Lens L₁
      module L₂ = Lens L₂
    field
      ≈-get : ∀ {x} → L₁.get x ≡ L₂.get x
      ≈-put : ∀ {x} {r} → L₁.put (x , r) ≡ L₂.put (x , r)

  _∙_ : Lens X S Y R → Lens Y R Z Q → Lens X S Z Q
  L₁ ∙ L₂ = record
    { get = L₂.get ∘ L₁.get
    ; put = λ (x , q) → L₁.put (x , (L₂.put ((L₁.get x) , q)))
    } where
      module L₁ = Lens L₁
      module L₂ = Lens L₂

  Lens⟨Set⟩ : Category (lsuc o) (lsuc o) o
  Lens⟨Set⟩ = record
    { Obj = Obj
    ; _⇒_ = _⇒_
    ; _≈_ = _≈_
    ; id = record { get = id ; put = proj₂ }
    ; _∘_ = flip _∙_
    ; assoc = record { ≈-get = refl ; ≈-put = refl }
    ; sym-assoc = record { ≈-get = refl ; ≈-put = refl }
    ; identityˡ = record { ≈-get = refl ; ≈-put = refl }
    ; identityʳ = record { ≈-get = refl ; ≈-put = refl }
    ; identity² = record { ≈-get = refl ; ≈-put = refl }
    ; equiv = record
      { refl = record { ≈-get = refl ; ≈-put = refl }
      ; sym = λ x≈y → let open _≈_ x≈y in record { ≈-get = sym ≈-get ; ≈-put = sym ≈-put }
      ; trans = λ x≈y y≈z → let
        module x≈y = _≈_ x≈y
        module y≈z = _≈_ y≈z in record { ≈-get = trans x≈y.≈-get y≈z.≈-get ; ≈-put = trans x≈y.≈-put y≈z.≈-put }
      }
    ; ∘-resp-≈ = λ g≈i f≈h → let
        module g≈i = _≈_ g≈i
        module f≈h = _≈_ f≈h in record { ≈-get = {! g≈i.≈-get  !} ; ≈-put = {!   !} }
    }

  LensMonoidal : Monoidal Lens⟨Set⟩
  LensMonoidal = record
    { ⊗ = record
      { F₀ = λ { ((A , B) , (A′ , B′)) → (A × A′) , (B × B′) }
      ; F₁ = λ { (L₁ , L₂) →
        let
          module L₁ = Lens L₁
          module L₂ = Lens L₂
        in record
          { get = λ (x , x′) → (L₁.get x , L₂.get x′)
          ; put = λ { ((x , x′) , (r , r′)) → (L₁.put (x , r) , L₂.put (x′ , r′)) }
          }
        }
      ; identity = record { ≈-get = λ {(_ , _)} → refl ; ≈-put = λ {(_ , _)} → refl  }
      ; homomorphism = record { ≈-get = refl ; ≈-put = refl }
      ; F-resp-≈ = λ (f≈g₁ , f≈g₂) → let
        module f≈g₁ = _≈_ f≈g₁
        module f≈g₂ = _≈_ f≈g₂ in record { ≈-get = {!   !} ; ≈-put = {!   !} }
      }
    ; unit = (⊤ , ⊤)
    ; unitorˡ = record { from = record { get = λ { (_ , p) → p } ; put = λ ((_ , a) , b) → (tt , b) }
                      ; to = record { get = λ { p → (tt , p) } ; put = λ (a , (_ , b)) → b }
                      ; iso = record { isoˡ = record { ≈-get = refl ; ≈-put = refl } ; isoʳ = record { ≈-get = refl ; ≈-put = refl } } }
    ; unitorʳ = record { from = record { get = λ { (p , _) → p } ; put = λ ((a , _) , b) → (b , tt) }
                      ; to = record { get = λ { p → (p , tt) } ; put = λ (a , (b , _)) → b }
                      ; iso = record { isoˡ = record { ≈-get = refl ; ≈-put = refl } ; isoʳ = record { ≈-get = refl ; ≈-put = refl } } }
    ; associator = record { from = record { get = λ ((a , b) , c) → a , (b , c)
                                          ; put = λ { ((a , b) , c , d , e) → (c , d) , e } }
                          ; to = record { get = λ (a , (b , c)) → (a , b) , c
                                        ; put = λ { ((a , b , c) , ((d , e) , f)) → d , e , f } }
                          ; iso = record { isoˡ = record { ≈-get = refl ; ≈-put = refl } ; isoʳ = record { ≈-get = refl ; ≈-put = refl } } }
    ; unitorˡ-commute-from = record { ≈-get = refl ; ≈-put = refl }
    ; unitorˡ-commute-to = record { ≈-get = refl ; ≈-put = refl }
    ; unitorʳ-commute-from = record { ≈-get = refl ; ≈-put = refl }
    ; unitorʳ-commute-to = record { ≈-get = refl ; ≈-put = refl }
    ; assoc-commute-from = record { ≈-get = refl ; ≈-put = refl }
    ; assoc-commute-to = record { ≈-get = refl ; ≈-put = refl }
    ; triangle = record { ≈-get = refl ; ≈-put = refl }
    ; pentagon = record { ≈-get = refl ; ≈-put = refl }
    }

module _ {P : Set o} where
  open import Categories.Category.Instance.Sets
  open import Categories.Monad
  open import Function using (id; flip; _∘_)

  Cont : Monad (Sets o)
  Cont = record
    { F = record
      { F₀ = λ X → (X → P) → P
      ; F₁ = λ f → (λ x w → x (w ∘ f))
      ; identity = refl
      ; homomorphism = refl
      ; F-resp-≈ = {!   !}
      }
    ; η = record
      { η = λ X → λ x f → f x
      ; commute = λ _ → refl
      ; sym-commute = λ _ → refl
      }
    ; μ = record
      { η = λ X → λ xpppp xp → {!   !}
      ; commute = {!   !}
      ; sym-commute = {!   !}
      }
    ; assoc = {!   !}
    ; sym-assoc = {!   !}
    ; identityˡ = {!   !}
    ; identityʳ = {!   !}
    }

module _ {P : Set o} where

  open import Categories.Category.Instance.Sets
  open import Categories.Category.Monoidal.Instance.Sets
  open import Categories.Category.Monoidal.Bundle using (MonoidalCategory)
  open import Categories.Functor.Monoidal using (IsMonoidalFunctor)
  open CategoryOfLens using (Lens⟨Set⟩; LensMonoidal)

  ⊗Sets : MonoidalCategory (lsuc o) o o
  ⊗Sets = record
    { U = Sets o
    ; monoidal = Product.Sets-Monoidal
    }

  ⊗LensSet : MonoidalCategory (lsuc o) (lsuc o) o
  ⊗LensSet = record
    { U = Lens⟨Set⟩
    ; monoidal = LensMonoidal
    }

  ∂ : Functor (Sets o) Lens⟨Set⟩
  ∂ = record
    { F₀ = λ X → X , (X → P)
    ; F₁ = λ f → record { get = f ; put = λ { (x , g) → λ z → g (f z) } }
    ; identity     = record { ≈-get = refl ; ≈-put = refl }
    ; homomorphism = record { ≈-get = refl ; ≈-put = refl }
    ; F-resp-≈ = λ f≡g → record { ≈-get = f≡g ; ≈-put = λ {_} {r} → {!  !} }
    }

  ∂-IsMonoidal : IsMonoidalFunctor ⊗Sets ⊗LensSet ∂
  ∂-IsMonoidal = record
    { ε = record
      { get = λ _ → tt
      ; put = λ _ → tt
      }
    ; ⊗-homo = record
      { η = λ _ → record
        { get = λ z → z
        ; put = λ { ((x , x') , n) → (λ z → n (z , x')) , λ y → n (x , y) }
        }
      ; commute = λ f → record { ≈-get = refl ; ≈-put = refl }
      ; sym-commute = λ f → record { ≈-get = refl ; ≈-put = refl }
      }
    ; associativity = record { ≈-get = refl ; ≈-put = refl }
    ; unitaryˡ = record { ≈-get = refl ; ≈-put = refl }
    ; unitaryʳ = record { ≈-get = refl ; ≈-put = refl }
    }

-- module _ where

--   ContParaM : ∀ (S R : Set o) → Set o → Set o
--   ContParaM S R A = (A → R) → S

--   μ : ∀ {T1 T2 T3 X} → ContParaM T1 T2 (ContParaM T2 T3 X) → ContParaM T1 T3 X
--   μ m f = m λ z → z f

--   KlHom : Obj → Obj → Set o
--   KlHom (X , S) (Y , R) = X → ContParaM S R Y

--   Cont-identity : ∀ {X} → KlHom X X
--   Cont-identity = λ z z₁ → z₁ z

--   Comp : ∀ {A B C : Obj} → KlHom A B → KlHom B C → KlHom A C
--   Comp f g = λ z z₁ → f z (λ z₂ → g z₂ z₁)

module _ where
  open CategoryOfLens using (Lens; Lens⟨Set⟩)
  open import Categories.Category.Construction.F-Algebras

  ∂-endo : Functor Lens⟨Set⟩ Lens⟨Set⟩
  ∂-endo = record
    { F₀ = λ (X , Y) → X , (X → Y)
    ; F₁ = λ f → let module f = Lens f in record { get = f.get ; put = λ {(x' , v) x → f.put ( x ,  v (f.get x))} }
    ; identity = record { ≈-get = refl ; ≈-put = refl }
    ; homomorphism = record { ≈-get = refl ; ≈-put = refl }
    ; F-resp-≈ = λ f≡g → record { ≈-get = {!   !} ; ≈-put = λ {_} {r} → {!  !} }
    }

  open Functor ∂-endo using (F₁; F₀; identity)
  open Category Lens⟨Set⟩ using (_∘_; _≈_)
  open import Function using (id)

  η : NaturalTransformation ∂-endo idF
  η = record
    { η = λ X → record { get = Function.id ; put = λ { (x , t) y → t } }
    ; commute = λ f → record { ≈-get = refl ; ≈-put = {! refl !} }
    ; sym-commute = {!   !}
    }

  μ : NaturalTransformation ∂-endo (∂-endo ∘F ∂-endo)
  μ = record
    { η = λ X → record { get = Function.id ; put = λ { (x , t) y → t x y } }
    ; commute = λ f → record { ≈-get = refl ; ≈-put = refl }
    ; sym-commute = λ f → record { ≈-get = refl ; ≈-put = refl }
    }

  module η = NaturalTransformation η
  module μ = NaturalTransformation μ

  -- assoc : ∀ {X} → μ.η X ∘ F₁ (μ.η X) ≈ μ.η X ∘ μ.η (F₀ X)
  -- assoc = ?

  -- sym-assoc : ∀ {X} → μ.η X ∘ μ.η (F₀ X) ≈ μ.η X ∘ F₁ (μ.η X)
  -- sym-assoc = ?

  -- identityˡ : ∀ {X} → μ.η X ∘ F₁ (η.η X) ≈ id
  -- identityˡ = ?

  -- identityʳ : ∀ {X} → μ.η X ∘ η.η (F₀ X) ≈ id
  -- identityʳ = ?

  ∂-alg : ∀ {P : Set o} → Category {!   !} {!   !} {!   !}
  ∂-alg {P} = {!  F-Algebras    !} --F-Algebras {!  ∂ {P} !}


-- module _ {o ℓ e} (C : MonoidalCategory o ℓ e) where

--   open MonoidalCategory C

--   open import Categories.Bicategory

--   record HomObj (A B : Obj) : Set (o ⊔ ℓ) where
--     field
--       M : Obj
--       ϕ : M ⊗₀ A ⇒ B

--   record 2-Cell {A B} (f g : HomObj A B) : Set {!   !} where
--     module f = HomObj f
--     module g = HomObj g

--     field
--       r : f.M ⇒ g.M
--       comm : {!   !} --? ∘ (? ⊗₁ ?) ≈ ?

--   Para : Bicategory (o ⊔ ℓ) ℓ e {!   !}
--   Para = record
--     { enriched = record
--       { Obj = Obj
--       ; hom = λ A B → record
--         { Obj = HomObj A B
--         ; _⇒_ = {!   !}
--         ; _≈_ = {!   !}
--         ; id = {!   !}
--         ; _∘_ = {!   !}
--         ; assoc = {!   !}
--         ; sym-assoc = {!   !}
--         ; identityˡ = {!   !}
--         ; identityʳ = {!   !}
--         ; identity² = {!   !}
--         ; equiv = {!   !}
--         ; ∘-resp-≈ = {!   !}
--         }
--       ; id = {!   !}
--       ; ⊚ = {!   !}
--       ; ⊚-assoc = {!   !}
--       ; unitˡ = {!   !}
--       ; unitʳ = {!   !}
--       }
--     ; triangle = {!   !}
--     ; pentagon = {!   !}
--     }

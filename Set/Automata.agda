module Set.Automata where

open import Data.Product using (map₂; _,_; _×_)
open import Data.Unit using (⊤)
open import Relation.Binary.PropositionalEquality using (_≡_)

private
  variable
    I O A B A′ B′ C D : Set

-- Mealy machine in Set
record Mealy (I : Set) (O : Set) : Set₁ where
  eta-equality
  field
    E : Set
    d : I × E → E
    s : I × E → O

-- Mealy machine in Set
record Moore (I : Set) (O : Set) : Set₁ where
  eta-equality
  field
    E : Set
    d : I × E → E
    s : E → O

-- morphism of Moore
record Moore⇒ (X Y : Moore I O) : Set₁ where
  module X = Moore X
  module Y = Moore Y
  field
    hom : X.E → Y.E
    d-eq : ∀ x → hom (X.d x) ≡ Y.d (map₂ hom x)
    s-eq : ∀ x → Y.s (hom x) ≡ X.s x

-- morphism of Mealy
record Mealy⇒ (M N : Mealy I O) : Set₁ where
  module M = Mealy M
  module N = Mealy N
  field
    hom : M.E → N.E
    d-eq : ∀ x → hom (M.d x) ≡ N.d (map₂ hom x)
    s-eq : ∀ x → N.s (map₂ hom x) ≡ M.s x

-- now with functional composition!
-- composition Mealy/Mealy
_⋄_ : Mealy B C → Mealy A B → Mealy A C
Y ⋄ X =
  let module X = Mealy X
      module Y = Mealy Y
   in record
        { E = X.E × Y.E
        ; d = λ { (a , e , e') → X.d (a , e) , Y.d (X.s (a , e) , e') }
        ; s = λ { (a , e , e') → Y.s (X.s (a , e) , e') }
        }

-- composition Mealy/Moore
_⋉_ : Moore B C → Mealy A B → Moore A C
Y ⋉ X =
  let module X = Mealy X
      module Y = Moore Y
   in record
        { E = X.E × Y.E
        ; d = λ { (a , (e , e')) → X.d (a , e) , Y.d (X.s (a , e) , e') }
        ; s = λ { (e , e') → Y.s e' }
        }

-- composition Moore/Mealy
_⋊_ : Mealy B C → Moore A B → Moore A C
Y ⋊ X =
  let module X = Moore X
      module Y = Mealy Y
   in record
        { E = X.E × Y.E
        ; d = λ { (a , (e , e')) → X.d (a , e) , Y.d (X.s e , e') }
        ; s = λ { (e , e') → Y.s (X.s e , e') }
        }

-- composition Moore/Moore ⋈
_⋈_ : Moore B C → Moore A B → Moore A C
Y ⋈ X =
  let module X = Moore X
      module Y = Moore Y
   in record
        { E = X.E × Y.E
        ; d = λ { (a , e , e') → X.d (a , e) , Y.d (X.s e , e') }
        ; s = λ { (e , e') → Y.s e' }
        }

idMealy : ∀ {A} → Mealy A A
idMealy {A} = record
  { E = ⊤
  ; d = λ { (a , tt) → tt }
  ; s = λ { (a , tt) → a }
  }

Mealy[_,_] : (f : A′ → A) → (g : B → B′) → Mealy A B → Mealy A′ B′
Mealy[ f , g ] M = let module M = Mealy M in record
  { E = M.E
  ; d = λ { (a , e) → M.d (f a , e) }
  ; s = λ { (a , e) → g (M.s (f a , e)) }
  }

{-# OPTIONS --without-K --safe #-}

open import Categories.Category

-- Lifting Properties
module Categories.Morphism.Lifts {o â e} (ð : Category o â e) where

open import Level

open Category ð
open Definitions ð

-- A pair of morphisms has the lifting property if every commutative
-- square admits a diagonal filler. We say that 'i' has the left lifting
-- property with respect to 'p', and that 'p' has the right lifting property
-- with respect to 'i'.
--
-- Graphically, the situation is as follows:
--
--      f
--   A ââââ> X
--   â     ^ â
--   â  â â±  â
-- i â   â±   â p
--   â  â±    â
--   V â±     V
--   B ââââ> Y
--      g
--
-- Note that the filler is /not/ required to be unique.
--
-- For ease of use, we define lifts in two steps:
-- * 'Filler' describes the data required to fill a /particular/ commutative square.
-- * 'Lifts' then quantifies over all commutative squares.

record Filler {A B X Y} {i : A â B} {f : A â X} {g : B â Y} {p : X â Y}
              (comm : CommutativeSquare i f g p) : Set (â â e) where
  field
    filler : B â X
    fill-commË¡ : filler â i â f
    fill-commÊ³ : p â filler â g

Lifts : â {A B X Y} â (i : A â B) â (p : X â Y) â Set (â â e)
Lifts i p = â {f g} â (comm : CommutativeSquare i f g p) â Filler comm

--------------------------------------------------------------------------------
-- Lifings of Morphism Classes

-- Shorthand for denoting a class of morphisms.
MorphismClass : (p : Level) â Set (o â â â suc p)
MorphismClass p = â {X Y} â X â Y â Set p

-- A morphism 'i' is called "projective" with respect to some morphism class 'J'
-- if it has the left-lifting property against every element of 'J'.
Projective : â {j} {A B} â MorphismClass j â (i : A â B) â Set (o â â â e â j)
Projective J i = â {X Y} â (f : X â Y) â J f â Lifts i f

-- Dually, a morphism 'i' is called "injective" with repsect to a morphism class 'J'
-- if it has the right-lifting property against every element of 'J'.
Injective : â {j} {A B} â MorphismClass j â (i : A â B) â Set (o â â â e â j)
Injective J i = â {X Y} â (f : X â Y) â J f â Lifts f i

-- The class of J-Projective morphisms.
Proj : â {j} (J : MorphismClass j) â MorphismClass (o â â â e â j)
Proj J = Projective J

-- The class of J-Injective morphisms.
Inj : â {j} (J : MorphismClass j) â MorphismClass (o â â â e â j)
Inj J = Injective J

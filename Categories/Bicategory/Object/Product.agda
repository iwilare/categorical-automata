{-# OPTIONS --without-K --safe #-}
open import Categories.Bicategory using (Bicategory)

module Categories.Bicategory.Object.Product {o ā e t} (š : Bicategory o ā e t) where

open import Level

open Bicategory š
open import Categories.Category using (_[_,_])
open import Categories.Morphism using (_ā_)
open import Categories.Morphism.HeterogeneousEquality
open import Categories.Morphism.Notation using (_[_ā_])

record Product  (A B : Obj) : Set (o ā ā ā e ā t) where
  infix 10 āØ_,_ā©ā āØ_,_ā©ā
  field
    AĆB : Obj
    Ļa : AĆB āā A
    Ļb : AĆB āā B
    āØ_,_ā©ā : ā {Ī} ā Ī āā A ā Ī āā B ā Ī āā AĆB
    āØ_,_ā©ā : ā {Ī}{fa ga : Ī āā A}{fb gb : Ī āā B}
           ā fa āā ga ā fb āā gb ā āØ fa , fb ā©ā āā āØ ga , gb ā©ā

    Ī²āa : ā {Ī} f g ā hom Ī A [ Ļa āā āØ f , g ā©ā  ā f ]
    Ī²āb : ā {Ī} f g ā hom Ī B [ Ļb āā āØ f , g ā©ā  ā g ]
    Ī²āa : ā {Ī}{fa ga fb gb}(Ī±a : hom Ī A [ fa , ga ])(Ī±b : hom Ī B [ fb , gb ])
        ā Along Ī²āa _ _ , Ī²āa _ _ [ Ļa ā· āØ Ī±a , Ī±b ā©ā ā Ī±a ] 
    Ī²āb : ā {Ī}{fa ga fb gb}(Ī±a : hom Ī A [ fa , ga ])(Ī±b : hom Ī B [ fb , gb ])
        ā Along Ī²āb _ _ , Ī²āb _ _ [ Ļb ā· āØ Ī±a , Ī±b ā©ā ā Ī±b ] 

    Ī·ā : ā {Ī} p ā hom Ī AĆB [ p ā āØ Ļa āā p , Ļb āā p ā©ā ]
    Ī·ā : ā {Ī}{p p'}(Ļ : hom Ī AĆB [ p , p' ])
       ā Along (Ī·ā _) , (Ī·ā _) [ Ļ ā āØ Ļa ā· Ļ , Ļb ā· Ļ ā©ā ]

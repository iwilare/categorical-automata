{-# OPTIONS --without-K --safe #-}
-- Various operations and proofs on morphisms between products

-- Perhaps a bit of overkill? There is so much here that it's impossible to remember
-- it all
open import Categories.Category

module Categories.Object.Product.Morphisms {o β e} (π : Category o β e) where

open import Function using (flip)
open import Level

open import Categories.Object.Product.Core π

open Category π
open HomReasoning

private
  variable
    A B C D E F : Obj
    f fβ² g gβ² h i : A β B

infix 10 [_]β¨_,_β© [_β_]_Γ_
infix 12 [[_]] [_]Οβ [_]Οβ

[[_]] : Product A B β Obj
[[ p ]] = Product.AΓB p

[_]β¨_,_β© : β (p : Product B C) β A β B β A β C β A β [[ p ]]
[ p ]β¨ f , g β© = Product.β¨_,_β© p f g

[_]Οβ : β (p : Product A B) β [[ p ]] β A
[_]Οβ = Product.Οβ

[_]Οβ : β (p : Product A B) β [[ p ]] β B
[_]Οβ = Product.Οβ

[_β_]_Γ_ : β (pβ : Product A C) (pβ : Product B D) β
             (A β B) β (C β D) β ([[ pβ ]] β [[ pβ ]])
[ pβ β pβ ] f Γ g  = [ pβ ]β¨ f β pβ.Οβ , g β pβ.Οβ β©
  where module pβ = Product pβ
        module pβ = Product pβ

idΓid : β (p : Product A B) β [ p β p ] id Γ id β id
idΓid p = begin
  β¨ id β Οβ , id β Οβ β© ββ¨ β¨β©-congβ identityΛ‘ identityΛ‘ β©
  β¨ Οβ , Οβ β©           ββ¨ Ξ· β©
  id                    β
  where open Product p

repackβ‘idΓid : β (pβ pβ : Product A B) β repack pβ pβ β [ pβ β pβ ] id Γ id
repackβ‘idΓid pβ pβ = βΊ (Product.β¨β©-congβ pβ identityΛ‘ identityΛ‘)

[_β_]ΟββΓ : β (pβ : Product A C)(pβ : Product B D) β
              Product.Οβ pβ β [ pβ β pβ ] f Γ g β f β Product.Οβ pβ
[_β_]ΟββΓ _ pβ = Product.projectβ pβ

[_β_]ΟββΓ : β (pβ : Product A C) (pβ : Product B D) β
              Product.Οβ pβ β [ pβ β pβ ] f Γ g β g β Product.Οβ pβ
[_β_]ΟββΓ _ pβ = Product.projectβ pβ

[_β_]Γ-congβ : β (pβ : Product A B) (pβ : Product C D) β
                 f β g β h β i β
                 [ pβ β pβ ] f Γ h β [ pβ β pβ ] g Γ i
[_β_]Γ-congβ pβ pβ fβg hβi =
    Product.β¨β©-congβ pβ (β-resp-β fβg Equiv.refl) (β-resp-β hβi Equiv.refl)

[_β_]Γββ¨β© : β (pβ : Product A B) (pβ : Product C D) β
              ([ pβ β pβ ] f Γ g) β [ pβ ]β¨ fβ² , gβ² β© β [ pβ ]β¨ f β fβ² , g β gβ² β©
[_β_]Γββ¨β© {f = f} {g = g} {fβ² = fβ²} {gβ² = gβ²} pβ pβ = begin
  [ pβ ]β¨ f β pβ.Οβ , g β pβ.Οβ β© β [ pβ ]β¨ fβ² , gβ² β© ββ¨ pβ.β-distribΚ³-β¨β© β©
  [ pβ ]β¨ (f β pβ.Οβ) β pβ.β¨_,_β© fβ² gβ²
        , (g β pβ.Οβ) β pβ.β¨_,_β© fβ² gβ² β©              ββ¨ pβ.β¨β©-congβ assoc assoc β©
  [ pβ ]β¨ f β pβ.Οβ β pβ.β¨_,_β© fβ² gβ²
        , g β pβ.Οβ β pβ.β¨_,_β© fβ² gβ² β©                ββ¨ pβ.β¨β©-congβ (β-resp-β Equiv.refl pβ.projectβ) (β-resp-β Equiv.refl pβ.projectβ) β©
  [ pβ ]β¨ f β fβ² , g β gβ² β©                           β
  where module pβ = Product pβ
        module pβ = Product pβ

[_]β¨β©β : β (p : Product A B) β [ p ]β¨ f , g β© β h β [ p ]β¨ f β h , g β h β©
[ p ]β¨β©β = βΊ (unique (sym-assoc β β-resp-βΛ‘ projectβ) (sym-assoc β β-resp-βΛ‘ projectβ))
  where open Product p

repackβrepackβid : β (pβ pβ : Product A B) β repack pβ pβ β repack pβ pβ β id
repackβrepackβid pβ pβ = [ pβ ]β¨β©β β pβ.β¨β©-congβ pβ.projectβ pβ.projectβ β pβ.Ξ·
  where module pβ = Product pβ
        module pβ = Product pβ

[_β_β_]ΓβΓ : β (pβ : Product A B) (pβ : Product C D) (pβ : Product E F) β
               ([ pβ β pβ ] g Γ i) β ([ pβ β pβ ] f Γ h) β [ pβ β pβ ] (g β f) Γ (i β h)
[_β_β_]ΓβΓ {g = g} {i = i} {f = f} {h = h} pβ pβ pβ = begin
  [ pβ ]β¨ g β pβ.Οβ , i β pβ.Οβ β© β [ pβ ]β¨ f β pβ.Οβ , h β pβ.Οβ β© ββ¨ [ pβ β pβ ]Γββ¨β© β©
  [ pβ ]β¨ g β f β pβ.Οβ , i β h β pβ.Οβ β©                           ββ¨ pβ.β¨β©-congβ sym-assoc sym-assoc β©
  [ pβ ]β¨ (g β f) β pβ.Οβ , (i β h) β pβ.Οβ β©                       β
  where module pβ = Product pβ
        module pβ = Product pβ
        module pβ = Product pβ

[_β_β_]repackβΓ : β (pβ : Product A B) (pβ : Product C D) (pβ : Product C D) β
                    repack pβ pβ β [ pβ β pβ ] f Γ g β [ pβ β pβ ] f Γ g
[_β_β_]repackβΓ {f = f} {g = g} pβ pβ pβ = begin
  repack pβ pβ β [ pβ β pβ ] f Γ g            ββ¨ repackβ‘idΓid pβ pβ β©ββ¨refl β©
  ([ pβ β pβ ] id Γ id) β ([ pβ β pβ ] f Γ g) ββ¨ [ pβ β pβ β pβ ]ΓβΓ β©
  [ pβ β pβ ] (id β f) Γ (id β g)             ββ¨ [ pβ β pβ ]Γ-congβ identityΛ‘ identityΛ‘ β©
  [ pβ β pβ ] f Γ g                           β

[_β_β_]repackβrepack : β (pβ pβ pβ : Product A B) β repack pβ pβ β repack pβ pβ β repack pβ pβ
[_β_β_]repackβrepack = repackβ

[_β_]_Γid : β (pβ : Product A C) (pβ : Product B C) β A β B β [[ pβ ]] β [[ pβ ]]
[ pβ β pβ ] f Γid = [ pβ β pβ ] f Γ id

[_β_]idΓ : β (pβ : Product A B) (pβ : Product A C) β B β C β [[ pβ ]] β [[ pβ ]]
[ pβ β pβ ]idΓ g = [ pβ β pβ ] id Γ g

first-id : β (p : Product A B) β [ p β p ] id Γid β id
first-id = idΓid

second-id : β (p : Product A B) β [ p β p ]idΓ id β id
second-id = idΓid

[_β_]Γidββ¨β© : β (pβ : Product B D) (pβ : Product C D) β
                  [ pβ β pβ ] f Γid β [ pβ ]β¨ fβ² , gβ² β© β [ pβ ]β¨ f β fβ² , gβ² β©
[_β_]Γidββ¨β© {f = f} {fβ² = fβ²} {gβ² = gβ²} pβ pβ = begin
  [ pβ β pβ ] f Γid β [ pβ ]β¨ fβ² , gβ² β© ββ¨ [ pβ β pβ ]Γββ¨β© β©
  [ pβ ]β¨ f β fβ² , id β gβ² β©            ββ¨ pβ.β¨β©-congβ Equiv.refl identityΛ‘ β©
  [ pβ ]β¨ f β fβ² , gβ² β©                 β
  where module pβ = Product pβ

[_β_]idΓββ¨β© : β (pβ : Product B D) (pβ : Product B E) β
                   [ pβ β pβ ]idΓ g β [ pβ ]β¨ fβ² , gβ² β© β [ pβ ]β¨ fβ² , g β gβ² β©
[_β_]idΓββ¨β© {g = g} {fβ² = fβ²} {gβ² = gβ²} pβ pβ = begin
  [ pβ β pβ ]idΓ g β [ pβ ]β¨ fβ² , gβ² β© ββ¨ [ pβ β pβ ]Γββ¨β© β©
  [ pβ ]β¨ id β fβ² , g β gβ² β©              ββ¨ pβ.β¨β©-congβ identityΛ‘ Equiv.refl β©
  [ pβ ]β¨ fβ² , g β gβ² β©                   β
  where module pβ = Product pβ

[_β_β_]ΓidβΓid : β (pβ : Product A D) (pβ : Product B D) (pβ : Product C D) β
                       [ pβ β pβ ] f Γid β [ pβ β pβ ] g Γid β [ pβ β pβ ] f β g Γid
[_β_β_]ΓidβΓid {f = f} {g = g} pβ pβ pβ = begin
  [ pβ β pβ ] f Γid β [ pβ β pβ ] g Γid ββ¨ [ pβ β pβ β pβ ]ΓβΓ β©
  [ pβ β pβ ] (f β g) Γ (id β id)       ββ¨ [ pβ β pβ ]Γ-congβ Equiv.refl identityΛ‘ β©
  [ pβ β pβ ] f β g Γid                 β

[_β_β_]idΓβidΓ : β (pβ : Product A B) (pβ : Product A C) (pβ : Product A D) β
                         [ pβ β pβ ]idΓ f β [ pβ β pβ ]idΓ g β [ pβ β pβ ]idΓ(f β g)
[_β_β_]idΓβidΓ {f = f} {g = g} pβ pβ pβ = begin
  [ pβ β pβ ]idΓ f β [ pβ β pβ ]idΓ g ββ¨ [ pβ β pβ β pβ ]ΓβΓ β©
  [ pβ β pβ ] (id β id) Γ (f β g)     ββ¨ [ pβ β pβ ]Γ-congβ identityΛ‘ Equiv.refl β©
  [ pβ β pβ ]idΓ (f β g)              β

[_β_,_β_]firstβsecond : β (pβ : Product A D) (pβ : Product B D)
                          (pβ : Product A C) (pβ : Product B C) β
                          [ pβ β pβ ] f Γid β [ pβ β pβ ]idΓ g β [ pβ β pβ ]idΓ g β [ pβ β pβ ] f Γid
[_β_,_β_]firstβsecond {f = f} {g = g} pβ pβ pβ pβ = begin
  [ pβ β pβ ] f Γid β [ pβ β pβ ]idΓ g ββ¨ [ pβ β pβ β pβ ]ΓβΓ β©
  [ pβ β pβ ] (f β id) Γ (id β g)      ββ¨ [ pβ β pβ ]Γ-congβ identityΚ³ identityΛ‘ β©
  [ pβ β pβ ] f Γ g                    βΛβ¨ [ pβ β pβ ]Γ-congβ identityΛ‘ identityΚ³ β©
  [ pβ β pβ ] (id β f) Γ (g β id)      βΛβ¨ [ pβ β pβ β pβ ]ΓβΓ β©
  [ pβ β pβ ]idΓ g β [ pβ β pβ ] f Γid β

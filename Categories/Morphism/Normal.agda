{-# OPTIONS --without-K --safe #-}

open import Categories.Category.Core
open import Categories.Object.Zero

-- Normal Mono and Epimorphisms
-- https://ncatlab.org/nlab/show/normal+monomorphism
module Categories.Morphism.Normal {o β e} (π : Category o β e) (π-Zero : Zero π) where

open import Level

open import Categories.Object.Kernel π-Zero
open import Categories.Object.Kernel.Properties π-Zero
open import Categories.Morphism π

open Category π

record IsNormalMonomorphism {A K : Obj} (k : K β A) : Set (o β β β e) where
  field
    {B} : Obj
    arr : A β B
    isKernel : IsKernel k arr

  open IsKernel isKernel public

  mono : Mono k
  mono = Kernel-Mono (IsKernelβKernel isKernel)

record NormalMonomorphism (K A : Obj) : Set (o β β β e) where
  field
    mor : K β A
    isNormalMonomorphism : IsNormalMonomorphism mor

  open IsNormalMonomorphism isNormalMonomorphism public

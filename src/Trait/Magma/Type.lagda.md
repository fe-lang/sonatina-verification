```agda
{-# OPTIONS --safe --erased-cubical #-}

module Trait.Magma.Type where

open import Prim.Type
open import Trait.Contr

record is-magma {ℓ} {A : Type ℓ} (_*_ : A → A → A) : Type ℓ where
  field
    magma-is-set : is-set A


```

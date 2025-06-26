```agda
{-# OPTIONS --safe --erased-cubical #-}

module Cat.Monoidal.Symmetric where

open import Prim.Type
open import Data.Category

record Monoidal-cat {o h} (C : Category o h) : Type (o ⊔ h) where
  no-eta-equality
  field
    Tensor : Functor ? C

```

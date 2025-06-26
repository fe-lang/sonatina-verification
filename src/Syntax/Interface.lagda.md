```agda
{-# OPTIONS --safe --erased-cubical #-}

module Syntax.Interface where

open import Prim.Type
open import HData.sList

record Intf {u} (A : Type u) : Type u where
  constructor _⇅_
  field
    exp : sList A
    imp : sList A

empty-interface : ∀ {u} {A : Type u} → Intf A
empty-interface = nil ⇅ nil

```

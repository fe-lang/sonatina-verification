```agda
{-# OPTIONS --safe --erased-cubical #-}

module Trait.Semantics where

open import Lib.Base


record has-bunched-connective {u v} {Res : Type u} (R : Res → Res → Res → Type v) : Type {!!} where
```

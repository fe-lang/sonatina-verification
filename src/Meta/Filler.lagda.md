```agda
{-# OPTIONS --safe --erased-cubical #-}

module Meta.Filler where

open import Prim.Type
open import Prim.Interval
open import Data.Path.Type

record Filler {u} (A : I → I → Type u)
  (w : A i0 i1) (x : A i0 i0) (y : A i1 i0) (z : A i1 i1) : Type u where
  field
    filler : ∀ i j → A i j
    @0 fill10 : filler i0 i1 ＝ w
    @0 fill00 : filler i0 i0 ＝ x
    @0 fill01 : filler i1 i0 ＝ y
    @0 fill11 : filler i1 i1 ＝ z


```

```agda
{-# OPTIONS --safe --erased-cubical #-}

module Trait.Logic.Bijection where

open import Prim.Type
open import Trait.Equiv

record is-logical-equiv {u v} {S : Type u} {T : Type v} : Type (u ⊔ v) where
  field
    fwd : T → S
    bk : T → S

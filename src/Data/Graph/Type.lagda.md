```agda
{-# OPTIONS --safe --erased-cubical #-}

module Data.Graph.Type where

open import Prim.Type
open import Control.Quiver

record Graph v e : Type₊ (v ⊔ e) where
  field
    Node : Type v
    Edge : Node → Node → Type e

instance
  Quiver-Graph : ∀ {v e} ⦃ G : Graph v e ⦄ → Quiver
  Quiver-Graph .Quiver.adj = {!!}
  Quiver-Graph .Quiver._=>_ = {!!}

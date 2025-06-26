```agda
{-# OPTIONS --safe --erased-cubical #-}

module Data.Graph.Base where

open import Prim.Prelude
open import Data.Graph.Type public


is-graph : ∀ {u v} → ∞-Graph u v → Type (u ⊔ v)
is-graph G = is-set G.Node × is-hom-set G.Edge where module G = ∞-Graph G

Graph : ∀ u v → Type₊ (u ⊔ v)
Graph u v = Σ g ∶ ∞-Graph u v , is-set (∞-Graph.Node g)

module Graph {u v} (G : Graph u v) where
  private module G = ∞-Graph (G .fst)
  Node : Type u
  Node = G.Node

  Edge : G.Node → G.Node → Type v
  Edge = G.Edge

```

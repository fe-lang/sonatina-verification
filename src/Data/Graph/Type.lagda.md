```agda
{-# OPTIONS --safe --cubical-compatible #-}

module Data.Graph.Type where

open import Prim.Type
open import Meta.Underlying

record Hypergraph v e : Type₊ (v ⊔ e) where
  field
    Node : Type v
    Edge : Node → Node → Type e

instance
  Underlying-Hypergraph : ∀ {u v} → Underlying (Hypergraph u v)
  Underlying-Hypergraph {u} .Underlying.ℓ-underlying = u
  Underlying-Hypergraph .Underlying.⌞_⌟ = Hypergraph.Node

-- record ∞-Graph-hom {u v} (G : Graph u v) : Type ? where
--   no-eta-equality
--   field
--     vertex : ⌞ G ⌟ → ⌞ H ⌟
--     edge : ∀ {x y} → G

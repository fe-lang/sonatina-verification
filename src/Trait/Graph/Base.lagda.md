```agda
{-# OPTIONS --safe --erased-cubical #-}

module Trait.Graph.Base where

open import Prim.Prelude

record Graphical {u} v (G : Type u) : Type (u ⊔ v ₊) where
  field
    Vtx : G → Type v
    empty : G
    overlay : G → G → G
    connect : G → G → G

  vertex : ∀ {a} → Vtx a → G
  vertex {a} = λ _ → a

open import Data.Graph.Type
open ∞-Graph

Graphical-Graph : ∀ {u v} → Graphical u (∞-Graph u v)
Graphical-Graph .Graphical.Vtx = Node 
Graphical-Graph .Graphical.empty .Node = 𝟘
Graphical-Graph .Graphical.empty .Edge = 𝟘-rec
Graphical-Graph .Graphical.overlay = {!!}
Graphical-Graph .Graphical.connect = {!!}

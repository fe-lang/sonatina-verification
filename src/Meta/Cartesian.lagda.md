```agda
{-# OPTIONS --safe --cubical-compatible #-}

module Meta.Cartesian where

open import Prim.Type
open import Meta.Underlying

record Cartesian {u v w} (A : Type u) (B : Type v) (Pro : A → B → Type w)
  : Typeω
  where
  infixr 7 _×_
  _×_ = Pro
  field
    cons : ∀ a b →  a × b

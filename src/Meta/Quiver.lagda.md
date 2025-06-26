```agda
{-# OPTIONS --safe --cubical-compatible #-}

module Meta.Quiver where

open import Prim.Type

record Quiver : Typeω where
  constructor quiver
  field
    {ℓ-hom} : Level → Level → Level
    Hom : ∀ {s t} → Type s → Type t → Type (ℓ-hom s t)

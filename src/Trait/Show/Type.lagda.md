```
{-# OPTIONS --safe --cubical-compatible #-}

module Trait.Show.Type where

open import Prim.Type
open import Data.String

record Show {ℓ} (A : Type ℓ) : Type ℓ where
  constructor mk-show
  field show : A → String
open Show ⦃...⦄ public

-- Show¹ = Show ¹
-- Show² = Show ²
-- Show³ = Show ³

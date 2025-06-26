{-# OPTIONS --cubical-compatible #-}
module Trait.Foldable.Instances where

open import Trait.Prelude
open import Trait.Functor
open import Trait.Semigroup
open import Trait.Monoid
open import Trait.Foldable.Type

instance
  Foldable-List : Foldable List
  Foldable-List .fold = go where go = λ where
    [] → ε
    (x ∷ []) → x
    (x ∷ xs@(_ ∷ _)) → x ◇ go xs

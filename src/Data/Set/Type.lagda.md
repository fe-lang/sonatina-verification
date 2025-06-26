```agda
{-# OPTIONS --safe --erased-cubical #-}

module Data.Set.Type where

open import Prim.Type
open import Lib.HLevel

Set : ∀ ℓ → Type₊ ℓ
Set ℓ = n-Type ℓ 2

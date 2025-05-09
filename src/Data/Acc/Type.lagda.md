```agda
{-# OPTIONS --safe --cubical-compatible #-}

module Data.Acc.Type where

open import Prim.Type

data Acc {ℓ ℓ'} {A : Type ℓ} (_<_ : A → A → Type ℓ') (x : A) : Type (ℓ ⊔ ℓ') where
  acc : ((y : A) → y < x → Acc _<_ y) → Acc _<_ x

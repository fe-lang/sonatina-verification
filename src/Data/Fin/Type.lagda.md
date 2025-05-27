Just as in Data.Irr, we concur with 1lab's definition of Fin for the
excellent reasons documented in https://1lab.dev/Data.Fin.Base.html

```agda
{-# OPTIONS --safe --cubical-compatible #-}

module Data.Fin.Type where

open import Prim.Type

open import Data.Nat.Type
open import Data.Irr.Type

record Fin (n : Nat) : Type where
  constructor fin
  field
    lower : Nat
    ⦃ bound ⦄ : Irr (lower < n)

open import Data.Irr.Type public using ( make-irr )
open Fin using ( lower ) public

pattern fzero = fin zero
pattern fone = fin (suc zero)

fsuc : ∀ {n} → Fin n → Fin (suc n)
fsuc (fin n ⦃ bound ⦄) =  fin (suc n) ⦃ s≤s <$> bound ⦄

```agda
{-# OPTIONS --safe --erased-cubical #-}

module Data.Nat.Base where

open import Prim.Type
open import Data.Pi
open import Data.Unit.Type using (⊤; tt)
open import Data.Nat.Type public

open import Meta.Operator

instance
  Plus-Nat : Plus λ _ _ → Nat
  Plus-Nat .Plus._+_ = Nat-add
  {-# DISPLAY Nat-add = _+_ #-}

  Asterisk-Nat : Asterisk (λ _ _ → Nat)
  Asterisk-Nat .Asterisk._*_ = Nat-mult
  {-# DISPLAY Nat-mult = _*_ #-}


foldn : ∀ {ℓ} {A : Type ℓ}
      → A → (A → A) → Nat → A
foldn c h zero = c
foldn c h (suc n) = h (foldn c h n)

plus : Nat → Nat → Nat
plus m = foldn m suc

mult : Nat → Nat → Nat
mult m = foldn 0 (plus m)

expn : Nat → Nat → Nat
expn m = foldn 1 (mult m)

```

This design pattern is lifted from 1Lab's version of this module, their
syntax notation for Sigma/Exists is very clever

```agda
{-# OPTIONS --safe --cubical-compatible #-}

module Meta.Underlying.Type where

open import Prim.Type

record Underlying {ℓ} (A : Type ℓ) : Typeω where
  field
    ℓ-underlying : Level
    ⌞_⌟   : A → Type ℓ-underlying

open Underlying ⦃ ... ⦄ public
{-# DISPLAY Underlying.⌞_⌟ _ X = ⌞ X ⌟ #-}

instance
  Underlying-Type : ∀ {ℓ} → Underlying (Type ℓ)
  Underlying-Type {ℓ} .ℓ-underlying = ℓ
  Underlying-Type .⌞_⌟  = id

  Underlying-Lift : ∀ {ℓ ℓ'} {A : Type ℓ}
                  → ⦃ ua : Underlying A ⦄
                  → Underlying (Lift ℓ' A)
  Underlying-Lift ⦃ ua ⦄ .ℓ-underlying = ua .ℓ-underlying
  Underlying-Lift .⌞_⌟ x = ⌞ x .lower ⌟

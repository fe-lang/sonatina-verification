```agda
{-# OPTIONS --safe --erased-cubical #-}

module Meta.Underlying.Instances where

open import Prim.Type
open import Prim.Data.Sigma
open import Trait.HLevel
open import Data.Category.Type

instance
  Underlying-n-Type : ∀ {ℓ k} → Underlying (n-Type ℓ k)
  Underlying-n-Type {ℓ} .ℓ-underlying = ℓ
  Underlying-n-Type .Underlying.⌞_⌟ = ∣_∣

  Underlying-Category : ∀ {o h} → Underlying (Category o h)
  Underlying-Category {o} .Underlying.ℓ-underlying = o
  Underlying-Category .⌞_⌟ = Category.Ob

```

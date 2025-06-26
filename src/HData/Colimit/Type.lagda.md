```agda
{-# OPTIONS --safe --erased-cubical #-}

module HData.Colimit.Type where

open import Prim.Type
open import Data.Nat.Type
open import Data.Path.Type

data Colimit {ℓ} (P : Nat → Type ℓ) (step : ∀ {n} → P n → P (suc n)) : Type ℓ where
  inc : ∀ {n} → P n → Colimit P step
  cong : ∀ {n} → (x : P n) → inc (step x) ＝ inc x


-- A variant of ∣∣≡∣∣ᴾ.
∣∣≡∣∣ : ∀ {ℓ} {P : Nat → Type ℓ} {step : ∀ {n} → P n → P (suc n)}
    → {n : Nat} (x : P n) → Path (Colimit P step) (inc (step x)) (inc x)
∣∣≡∣∣ x = {!!}

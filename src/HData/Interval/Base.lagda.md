The internalized interval as a higher inductive type

```agda
{-# OPTIONS --safe --erased-cubical #-}

module HData.Interval.Base where

open import Prim.Type
open import Data.Path.Type

open import Lib.HLevel.Base
open import Data.Bool.Type
open import HData.PropTrunc.Type

data 𝕀 : Type where
  ₀ : 𝕀
  ₁ : 𝕀
  seg : ₀ ＝ ₁

ind-𝕀 : ∀ {ℓ} (P : 𝕀 → Type ℓ) (b₀ : P ₀) (b₁ : P ₁)
      → ∂ i ↦ P (seg i) , b₀ ＝ b₁
      → (i : 𝕀) → P i
ind-𝕀 P b₀ b₁ bₛ ₀ = b₀
ind-𝕀 P b₀ b₁ bₛ ₁ = b₁
ind-𝕀 P b₀ b₁ bₛ (seg i) = bₛ i

rec-𝕀 : ∀ {ℓ} {A : Type ℓ} → (x y : A) → x ＝ y → (i : 𝕀) → A
rec-𝕀 x y p ₀ = x
rec-𝕀 x y p ₁ = y
rec-𝕀 x y p (seg i) = p i

_⊗_ : 𝕀 → 𝕀 → 𝕀
₀ ⊗ j = ₀
₁ ⊗ j = j
seg i ⊗ ₀ = ₀
seg i ⊗ ₁ = seg i
seg i ⊗ seg j = seg (i ∧ j)

_⊕_ : 𝕀 → 𝕀 → 𝕀
₀ ⊕ j = j
₁ ⊕ j = ₁
seg i ⊕ ₀ = seg i
seg i ⊕ ₁ = ₁
seg i ⊕ seg j = seg (i ∨ j)

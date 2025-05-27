```agda
{-# OPTIONS --safe --cubical-compatible --two-level #-}

module Prim.SSet where

open import Prim.Type

data _≡_ {ℓ} {A : SSet ℓ} (x : A) : A → SSet ℓ where
  srefl : x ≡ x

SEq : ∀ {ℓ} (A : SSet ℓ) → A → A → SSet ℓ
SEq A = _≡_ {A = A}

SEq-K : ∀ {ℓ} {A : SSet ℓ} {x y : A} (p q : x ≡ y) → p ≡ q
SEq-K srefl srefl = srefl

```

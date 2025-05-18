```agda
{-# OPTIONS --safe --erased-cubical #-}

module Trait.Logic.Unique where

open import Prim.Type
open import Prim.Interval.Core
open import Prim.Data.Path
open import Trait.HLevel.Base
open import Trait.Logic.Exists

open import Prim.Data.Sigma public
open import Prim.Data.Contr public

infixr 5 ∃!-syntax

-- Unique existence
∃! : ∀ {u v} {A : Type u} (B : A → Type v) → Type (u ⊔ v)
∃! B = is-contr (Σ B)

unique : ∀ {u v} {A : Type u} {B : A → Type v} → Σ B → is-prop (Σ B) → ∃! B
unique = contractible

∃!-syntax : ∀ {ℓ ℓ'} {A : Type ℓ} ⦃ _ : Underlying A ⦄
          → (X : A) (F : ⌞ X ⌟ → Type ℓ') → Type _
∃!-syntax X F = is-contr (Sigma ⌞ X ⌟ F)
syntax ∃!-syntax A (λ x → M) = ∃! x ∶ A , M
{-# DISPLAY ∃!-syntax _ B = ∃! B #-}

unique→exists : ∀ {u v} {A : Type u} {B : A → Type v}
              → ∃! B → ∃ B
unique→exists ub = inc (ub .ctr)

∃!-map : ∀ {u v w} {A : Type u} {P : A → Type v} {Q : A → Type w}
       → (f : Σ P → Σ Q) → is-prop (Σ Q) → ∃! P → ∃! Q
∃!-map {P} {Q} f fprop = λ z → f (z .ctr) , fprop (f (z .ctr))

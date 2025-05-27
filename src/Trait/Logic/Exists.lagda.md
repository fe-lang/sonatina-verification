```agda
{-# OPTIONS --safe --erased-cubical #-}

module Trait.Logic.Exists where

open import Prim.Type
open import Trait.HLevel.Base

open import Data.Sigma.Type public
open import HData.Trunc.Prop public

infix 5 ∃-syntax

∃ : ∀ {u v} {A : Type u} → (A → Type v) → Type (u ⊔ v)
∃ B = ∥ Σ B ∥

∃-syntax : ∀ {ℓ ℓ'} {A : Type ℓ} ⦃ _ : Underlying A ⦄
         → (X : A) (F : ⌞ X ⌟ → Type ℓ') → Type _
∃-syntax X F = ∥ Sigma ⌞ X ⌟ F ∥
syntax ∃-syntax A (λ x → M) = ∃ x ∶ A , M
{-# DISPLAY ∃-syntax _ B = ∃ B #-}

∃-ind : ∀ {u v w} {A : Type u} {B : A → Type v} (P : ∃ B → Type w)
      → (∀ z → is-prop (P z)) → (∀ z → P (inc z)) → (z : ∃ B) → P z
∃-ind = Pt-ind

∃-map : ∀ {u v w} {A : Type u} {P : A → Type v} {Q : A → Type w}
      → (∀ x → P x → Q x) → ∃ P → ∃ Q
∃-map η = Pt-map (λ z → z .fst , η (z .fst) (z .snd))

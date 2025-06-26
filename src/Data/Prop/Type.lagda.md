```agda
{-# OPTIONS --safe --erased-cubical #-}

module Data.Prop.Type where

open import Prim.Type
open import Trait.Equiv
open import Lib.Fiber
open import Data.Path.Type
open import Trait.Contr
open import Data.Sigma.Type

open import Data.Empty.Type
open import Data.Unit.Type

open import Trait.Underlying

open import Lib.HLevel

Prop : ∀ ℓ → Type₊ ℓ
Prop ℓ = n-Type ℓ 1

True : ∀ {u} → Prop u
True .ntype = 𝟙
True .is-tr x y = refl

False : ∀ {u} → Prop u
False .ntype = 𝟘
False .is-tr ()

module _ {u v} {P : Type u} {Q : Type v}
  (pprop : is-prop P) (qprop : is-prop Q)
  (f : P → Q) (g : Q → P)
  where
  private
    γ : has-inverse f
    γ .inverse = g
    γ .inverse-sec = λ x → pprop (g (f x)) x
    γ .inverse-retr = λ y → qprop (f (g y)) y

  is-prop-is-equiv : P ≃ Q
  is-prop-is-equiv .fst = f
  is-prop-is-equiv .snd = inverse→equiv f γ

  prop-fiber : (b : Q) → is-contr (fiber f b)
  prop-fiber b = inverse→contr-fibers γ b

-- Prop-is-equiv : ∀ {u v} (P : Prop u) (Q : Prop v) → P ≃ Q
-- Prop-is-equiv P Q = ?

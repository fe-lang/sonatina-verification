```agda

{-# OPTIONS --safe --erased-cubical #-}

module Trait.Semigroup.Type where

open import Prim.Type
open import Data.Path.Type
open import Trait.Contr

open import Trait.Magma.Type

record is-semigroup {ℓ} {A : Type ℓ} (_*_ : A → A → A) : Type ℓ where
  field
    has-magma : is-magma _*_
    scomm   : ∀ x y → x * y ＝ y * x
    sassoc : ∀ x y z → (x * y) * z ＝ x * (y * z)

-- module _ {ℓ} {A : Type ℓ} ⦃ _ : Semigroup A ⦄ where
--   sym-sassoc : ∀ (x y z : A) → (x ◇ (y ◇ z)) ＝ ((x ◇ y) ◇ z)
--   sym-sassoc x y z = sym (sassoc x y z)

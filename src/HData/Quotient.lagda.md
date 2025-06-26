From the presentation in the paper "Algebraic Effects Meet Hoare Logic
in Cubical Agda" by Donnacha Oisín Kidney, Zhixuan Yang, and Nicolas Wu

```agda
{-# OPTIONS --safe --erased-cubical #-}

module HData.Quotient where

open import Prim.Type
open import Data.Path.Type
open import Trait.HLevel.Base

data _/_ {o h} (A : Type o) (_~_ : A → A → Type h) : Type (o ⊔ h) where
  inc/ : A → A / _~_
  eq/ : ∀ x y → x ~ y → inc/ x ＝ inc/ y
  squash/ : is-set (A / _~_)

rec/ : ∀ {o h v} {A : Type o}
     → (R : A → A → Type h)
     → {B : Type v} → is-set B
     → (f : A → B) → (∀ x y → R x y → f x ＝ f y)
     → A / R → B
rec/ {A} R {B} bset f cong = φ where
  φ : A / R → B
  φ (inc/ x) = f x
  φ (eq/ x y p i) = cong x y p i
  φ (squash/ x y p q i j) = bset (φ x) (φ y) (λ k → φ (p k)) (λ k → φ (q k)) i j

```agda
{-# OPTIONS --safe --erased-cubical #-}

module Data.Sum.Base where

open import Prim.Type
open import Data.Path.Type
open import Data.Empty.Type

open import Data.Sum.Type public

inl-inj : ∀ {u v} {A : Type u} {B : Type v}
        → {x y : A} → inl {A = A} {B = B} x ＝ inl y
        → (B → A) → x ＝ y
inl-inj p g i = cases id g (p i)

inr-inj : ∀ {u v} {A : Type u} {B : Type v}
        → {x y : B} → inr {A = A} {B = B} x ＝ inr y
        → (A → B) → x ＝ y
inr-inj p g i = cases g id (p i)

inl-inr-inj : ∀ {u v} {A : Type u} {B : Type v}
            → {x : A} {y : B}
            → ¬ (inl {A = A} {B = B} x ＝ inr y)
inl-inr-inj {A} {B} p = {!!} where
  γ : A ⊎ B → ⊥
  γ = {!!}



```

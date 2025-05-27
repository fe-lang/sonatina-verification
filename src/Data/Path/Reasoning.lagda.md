Compact and portable path reasoning syntax

```agda
{-# OPTIONS --safe --erased-cubical #-}

module Data.Path.Reasoning where

open import Prim.Type
open import Meta.Cut
open import Data.Pi using (flip)
open import Data.Path.Type

-- This formulation of path reasoning syntax derives from the
-- Erased Cubical formalization by Nils Anders Danielsson
infixr -2 path-reasoning-syntax
path-reasoning-syntax : ∀ {ℓ} {A : Type ℓ} x {y z : A}
                      → y ＝ z → x ＝ y → x ＝ z
path-reasoning-syntax x = flip (_∙_ {x = x})
syntax path-reasoning-syntax x q p = x ＝⟨ p ⟩ q

infix -1 finally
finally : ∀ {ℓ} {A : Type ℓ} (x y : A) → x ＝ y → x ＝ y
finally _ _ x＝y = x＝y

syntax finally x y x≡y = x ＝⟨ x≡y ∣ y ∎

infixr -2 double-comp-reasoning-syntax
double-comp-reasoning-syntax :
  ∀ {ℓ} {A : Type ℓ} (w x y z : A) → y ＝ z → x ＝ y → w ＝ x → w ＝ z
double-comp-reasoning-syntax w x y z r q p = p ∙∙ q ∙∙ r

syntax double-comp-reasoning-syntax w x y z r q p = w □⟨ p ⟩ x □⟨ q ⟩ y □⟨ r ⟩ z ∎

Compact and portable path reasoning syntax

```agda
{-# OPTIONS --safe --erased-cubical #-}

module Prim.Reasoning where

open import Prim.Type
open import Prim.Pi using (flip)
open import Prim.Kan using (path-comp)
open import Prim.Data.Path using (_＝_)

-- This formulation of path reasoning syntax derives from the
-- Erased Cubical formalization by Nils Anders Danielsson
infixr -2 path-reasoning-syntax
path-reasoning-syntax : ∀ {ℓ} {A : Type ℓ} x {y z : A}
                      → y ＝ z → x ＝ y → x ＝ z
path-reasoning-syntax x = flip (path-comp {x = x})
syntax path-reasoning-syntax x q p = x ＝⟨ p ⟩ q

infix -1 finally
finally : ∀ {ℓ} {A : Type ℓ} (x y : A) → x ＝ y → x ＝ y
finally _ _ x＝y = x＝y

syntax finally x y x≡y = x ＝⟨ x≡y ∣ y ∎

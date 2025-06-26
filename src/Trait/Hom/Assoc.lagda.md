```agda
{-# OPTIONS --safe --erased-cubical #-}

open import Meta.Object
module Trait.Hom.Assoc {O : Object} (C : Composable O) where

open import Prim.Type
open import Prim.Interval
open import Data.Sigma.Type
open import Data.Path.Type
open import Data.Path.Reasoning
open import Trait.Equiv using (is-equiv; _≃_; eqv-inv)

private module C where
  open Object O public
  open Composable C public

Associatvity : ∀ {w x y z} (f : C.₁ w x) (g : C.₁ x y) (h : C.₁ y z)
             → Type (C.adj C.lvl)
Associatvity f g h = f ∙ (g ∙ h) ＝ (f ∙ g) ∙ h

```
These definitions are taken from Sterling's Duploid modules on
TypeTopology:

https://martinescardo.github.io/TypeTopology/Duploids.DeductiveSystem.html
```
module _ {x y} (f : C.₁ x y) where
  is-thunkable : Type C.ℓ
  is-thunkable = {a b : C.₀} (g : C.₁ y a) (h : C.₁ a b)
               → f ∙ (g ∙ h) ＝ (f ∙ g) ∙ h

  is-linear : Type C.ℓ
  is-linear = {u v : C.₀} (g : C.₁ v x) (h : C.₁ u v)
            → h ∙ (g ∙ f) ＝ (h ∙ g) ∙ f

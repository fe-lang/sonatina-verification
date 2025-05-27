The syntactic structure of a monoid without bells and whistles

```agda
{-# OPTIONS --safe --cubical-compatible #-}

module Meta.Append where

open import Prim.Type
open import Meta.Idiom public

record Append {ℓ} (A : Type ℓ) : Type ℓ where
  infixr 8 _++_

  field
    mempty : A
    _++_   : A → A → A

open Append ⦃ ... ⦄ public

```

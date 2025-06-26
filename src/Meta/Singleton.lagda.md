Notation typeclasses for the notion of Singletons

```agda
{-# OPTIONS --safe --cubical-compatible #-}

module Meta.Singleton where

open import Prim.Type
open import Meta.Idiom

record Singleton (M : Effect) : Typeω where
  private module M = Effect M
  field
    [_] : ∀ {ℓ} {A : Type ℓ} → A → M.₀ A
    [] : ∀ {ℓ} {A : Type ℓ} → M.₀ A

open Singleton ⦃ ... ⦄ public

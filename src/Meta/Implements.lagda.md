A metaprogramming interface for types that are equivalent to the
data of a Sigma record; we say that the sigma type B 'implements'
the data of C. We generalize even from Sigma records though, as
we will show that Sigma trivially implements itself.

```agda
{-# OPTIONS --safe --erased-cubical #-}

module Meta.Implements where

open import Prim.Type
open import Prim.Interval
open import Data.Pi
open import Data.Path.Type
open import Data.Sigma.Type

record Impl {u v} {A : Type u} (B : A → Type v) (C : A → Type v) : Typeω where
  no-eta-equality
  field
    to : ∀ {x} → B x → C x
    from : ∀ {x} → C x → B x

  to-Σ : Σ B → Σ C
  to-Σ (x , b) = x , to b

  from-Σ : Σ C → Σ B
  from-Σ (x , c) = x , from c

open Impl ⦃ ... ⦄ public

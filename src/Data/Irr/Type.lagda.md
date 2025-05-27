Strict propositional truncations, defined just as in 1lab

  https://1lab.dev/Data.Irr.html

```agda

{-# OPTIONS --safe --cubical-compatible #-}

module Data.Irr.Type where

open import Prim.Type
open import Meta.Idiom

record Irr {ℓ} (A : Type ℓ) : Type ℓ where
  constructor forget
  field
    .lower : A

instance
  make-irr : ∀ {ℓ} {A : Type ℓ} ⦃ x : A ⦄ → Irr A
  make-irr ⦃ x ⦄ = forget x
  {-# INCOHERENT make-irr #-}

  Map-Irr : Map (eff Irr)
  Map-Irr .Map.map = λ where f (forget lower) → forget ( f lower )

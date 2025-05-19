```agda
{-# OPTIONS --safe --erased-cubical #-}

module Prim.Data.Contr where

open import Prim.Type
open import Prim.Data.Path using (_＝_; Path; fiber)
open import Prim.Data.Nat using (Nat; zero; suc)

record is-contr {ℓ} (A : Type ℓ) : Type ℓ where
  constructor _,_
  field
    ctr : A
    paths : (y : A) → ctr ＝ y

open is-contr public

-- Alternative constructor for is-contr utilizing is-prop. is-prop is formally
-- defined in Trait.HLevel
contractible : ∀ {ℓ} {A : Type ℓ} → ((x y : A) → x ＝ y) → A →  is-contr A
contractible p c .ctr = c
contractible p c .paths = p c

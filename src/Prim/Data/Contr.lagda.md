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
contractible : ∀ {ℓ} {A : Type ℓ} → A → ((x y : A) → x ＝ y) → is-contr A
contractible c p .ctr = c
contractible c p .paths = p c

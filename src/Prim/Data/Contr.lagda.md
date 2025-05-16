```agda
{-# OPTIONS --safe --erased-cubical #-}

module Prim.Data.Contr where

open import Prim.Type
open import Prim.Data.Path using (_＝_; Path; fiber)
open import Prim.Data.Nat using (Nat; zero; suc)
open import Prim.Data.Sigma

record is-contr {ℓ} (A : Type ℓ) : Type ℓ where
  constructor _,_
  field
    ctr : A
    paths : (y : A) → ctr ＝ y

open is-contr public

is-prop : ∀ {ℓ} → Type ℓ → Type ℓ
is-prop A = (x y : A) → x ＝ y

-- Alternative constructor for is-contr
contractible : ∀ {ℓ} {A : Type ℓ} → A → is-prop A → is-contr A
contractible c p .ctr = c
contractible c p .paths = p c

is-set : ∀ {ℓ} → Type ℓ → Type ℓ
is-set A = (x y : A) → is-prop (x ＝ y)

-- Unique existence
∃! : ∀ {u v} {A : Type u} (B : A → Type v)
   → Type (u ⊔ v)
∃! B = is-contr (Σ B)

```agda
{-# OPTIONS --safe --erased-cubical #-}

module Prim.Data.Contr where

open import Prim.Type
open import Prim.Data.Path using (_＝_; Path)
open import Prim.Data.Nat using (Nat; zero; suc)

record is-contr {ℓ} (A : Type ℓ) : Type ℓ where
  constructor _,_
  field
    ctr : A
    paths : (y : A) → ctr ＝ y

open is-contr public

is-prop : ∀ {ℓ} → Type ℓ → Type ℓ
is-prop A = (x y : A) → x ＝ y

is-set : ∀ {ℓ} → Type ℓ → Type ℓ
is-set A = {x y : A} (p q : x ＝ y) → p ＝ q

is-hlevel-suc : ∀ {ℓ} → Nat → Type ℓ → Type ℓ
is-hlevel-suc zero A = is-prop A
is-hlevel-suc (suc n) A = {x y : A} → is-hlevel-suc n (x ＝ y)

is-hlevel : ∀ {ℓ} → Nat → Type ℓ → Type ℓ
is-hlevel zero A = is-contr A
is-hlevel (suc n) A = is-hlevel-suc n A

-- use for situations where we'd calculate too many implicits
is-hlevelₑ : ∀ {ℓ} → Nat → Type ℓ → Type ℓ
is-hlevelₑ zero A = is-contr A
is-hlevelₑ (suc zero) A = is-prop A
is-hlevelₑ (suc (suc n)) A = (x y : A) → is-hlevel n (Path A x y)

```

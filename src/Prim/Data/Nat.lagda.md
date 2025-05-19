```agda

{-# OPTIONS --safe --cubical-compatible #-}

module Prim.Data.Nat where

open import Prim.Type using ( Type )
open import Prim.Literals
open import Prim.Data.Unit using (⊤; tt)
open import Agda.Builtin.Nat renaming ( _<_ to _<₂_ ) public

infix 7 _≤_ _<_

instance
  Number-Nat : Number Nat
  Number-Nat .Number.Constraint = λ _ → ⊤
  Number-Nat .Number.fromNat n = n

Nat-ind : ∀ {ℓ} (P : Nat → Type ℓ)
        → P 0 → (∀ k → P k → P (suc k))
        → (n : Nat) → P n
Nat-ind P b s 0 = b
Nat-ind P b s (suc n) = s n (Nat-ind P b s n)

data _≤_ : Nat → Nat → Type where
  instance 0≤x : ∀ {x} → 0 ≤ x
  s≤s : ∀ {x y} → x ≤ y → suc x ≤ suc y

open _≤_ public

_<_ : Nat → Nat → Type
m < n = suc m ≤ n

instance
  0<suc : ∀ {n} → 0 < suc n
  0<suc = s≤s 0≤x

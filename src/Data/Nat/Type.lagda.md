```agda

{-# OPTIONS --safe --cubical-compatible #-}

module Data.Nat.Type where

open import Prim.Type using ( Type )
open import Meta.Literals public
open import Meta.Operator public

open import Data.Unit.Type public using (⊤; tt)
open import Agda.Builtin.Nat public
  renaming ( _<_ to _<₂_
           ; _+_ to Nat-add
           ; _*_ to Nat-mult
           ; _-_ to Nat-monus
           )

infix 7 _≤_ _<_

Nat-ind : ∀ {ℓ} (P : Nat → Type ℓ)
        → P zero → (∀ k → P k → P (suc k))
        → (n : Nat) → P n
Nat-ind P b s zero = b
Nat-ind P b s (suc n) = s n (Nat-ind P b s n)

data _≤_ : Nat → Nat → Type where
  instance 0≤x : ∀ {x} → zero ≤ x
  s≤s : ∀ {x y} → x ≤ y → suc x ≤ suc y

open _≤_ public

_<_ : Nat → Nat → Type
m < n = suc m ≤ n

instance
  0<suc : ∀ {n} → zero < suc n
  0<suc = s≤s 0≤x

  Number-Nat : Number Nat
  Number-Nat .Number.Constraint = λ _ → ⊤
  Number-Nat .Number.fromNat n = n

  Plus-Nat : Plus λ _ _ → Nat
  Plus-Nat .Plus._+_ = Nat-add
  {-# DISPLAY Nat-add = _+_ #-}

  Asterisk-Nat : Asterisk (λ _ _ → Nat)
  Asterisk-Nat .Asterisk._*_ = Nat-mult
  {-# DISPLAY Nat-mult = _*_ #-}

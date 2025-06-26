```agda

{-# OPTIONS --safe --cubical-compatible #-}

module Data.Nat.Type where

open import Prim.Type using ( Type )
open import Data.Unit.Type using (⊤; tt)

open import Meta.Literals

open import Agda.Builtin.Nat public
  renaming ( _<_ to _<₂_
           ; _+_ to Nat-add
           ; _*_ to Nat-mult
           ; _-_ to Nat-monus
           )

infix 7 _≤ₙ_ _<ₙ_

Nat-ind : ∀ {ℓ} (P : Nat → Type ℓ)
        → P zero → (∀ k → P k → P (suc k))
        → (n : Nat) → P n
Nat-ind P b s zero = b
Nat-ind P b s (suc n) = s n (Nat-ind P b s n)

data _≤ₙ_ : Nat → Nat → Type where
  instance 0≤x : ∀ {x} → zero ≤ₙ x
  s≤s : ∀ {x y} → x ≤ₙ y → suc x ≤ₙ suc y

open _≤ₙ_ public

_<ₙ_ : Nat → Nat → Type
m <ₙ n = suc m ≤ₙ n

instance
  Number-Nat : Number Nat
  Number-Nat .Number.Constraint = λ _ → ⊤
  Number-Nat .Number.fromNat n = n

  0<suc : ∀ {n} → zero <ₙ suc n
  0<suc = s≤s 0≤x


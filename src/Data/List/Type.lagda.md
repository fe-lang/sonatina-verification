```agda

{-# OPTIONS --safe --cubical-compatible #-}

module Data.List.Type where

open import Prim.Type

open import Agda.Builtin.List renaming ( _∷_ to infixr 40 _∷_) public
open import Prim.Data.Nat

infixr 60 _++_

_++_ : ∀ {u} {A : Type u} → List A → List A → List A
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

length : ∀ {u} {A : Type u} → List A → Nat
length [] = zero
length (x ∷ xs) = suc (length xs)

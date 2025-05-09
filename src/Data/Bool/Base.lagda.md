```agda

{-# OPTIONS --safe --cubical-compatible #-}

module Data.Bool.Base where

open import Prim.Type
open import Data.Empty.Type using (⊥)
open import Data.Unit.Type using (⊤)

open import Data.Bool.Type public

Tt : Bool → Type
Tt false = ⊥
Tt true = ⊤

not : Bool → Bool
not false = true
not true = false

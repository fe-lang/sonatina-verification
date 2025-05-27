```agda

{-# OPTIONS --safe --cubical-compatible #-}

module Data.Dec.Type where

open import Prim.Type
open import Data.Empty.Type

data Dec {a} (P : Type a) : Type a where
  yes : P → Dec P
  no  : ¬ P → Dec P

infix 0 if-yes_then_else_ if-no_then_else_
if-yes_then_else_ : ∀ {a b} {A : Type a} {B : Type b} → Dec A → B → B → B
if-yes yes _ then x else _ = x
if-yes no  _ then _ else y = y

if-no_then_else_ : ∀ {a b} {A : Type a} {B : Type b} → Dec A → B → B → B
if-no d then x else y = if-yes d then y else x

From-dec : ∀ {a} {P : Type a} → Dec P → Type a
From-dec {P = P} (yes _) = P
From-dec {P = P} (no  _) = ¬ P

from-dec : ∀ {a} {P : Type a} (d : Dec P) → From-dec d
from-dec (yes x) = x
from-dec (no  x) = x

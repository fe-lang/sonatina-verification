```agda
{-# OPTIONS --safe --erased-cubical #-}


open import Data.Category.Type

module Data.Category.Isomorphism {o h} (C : Category o h) where

open import Prim.Type
open import Prim.Data.Sigma
open import Prim.Path

open import Prim.Path using ( tr )

open import Data.Semicategory.Iso (C .Category.base) public
open Category C

refl-iso : ∀ x → x ≅ x
refl-iso x = idn x , iso x

from-path : ∀ {x y} → x ＝ y → x ≅ y
from-path {x} p = tr (Iso x) p (refl-iso x)

```agda
{-# OPTIONS --safe --erased-cubical #-}

module Data.Semicategory.Meta where

open import Prim.Type

open import Data.Semicategory.Type
open import Prim.Path
open import Lib.Path.Groupoid using ( assoc-path )

ωSemigrpd : ∀ u → Semicategory (u ₊) (u ₊)
ωSemigrpd u .Semicategory.Ob = Type u
ωSemigrpd u .Semicategory.Hom = _＝_
ωSemigrpd u .Semicategory._⨾_ = _∙_
ωSemigrpd u .Semicategory.assoc  = assoc-path

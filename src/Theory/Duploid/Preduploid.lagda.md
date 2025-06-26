```agda
{-# OPTIONS --safe --erased-cubical #-}

module Theory.Duploid.Preduploid where

open import Prim.Type
open import Data.Pi using ( flip )

open import Data.Path.Type
open import Trait.Equiv
open import Data.Bool.Type

open import Theory.Duploid.Type

record Preduploid o h : Type₊ (o ⊔ h) where
  field
    lang : Lang o h

  open Data.Sequent.Properties lang
  field
    ax : ∀ A → is-polarized A

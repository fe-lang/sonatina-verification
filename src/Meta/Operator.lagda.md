```agda
{-# OPTIONS --safe --cubical-compatible #-}

module Meta.Operator where

open import Prim.Type

module _ {u v w} {A : Type u} {B : Type v} (C : A → B → Type w) where
  record Plus : Type (u ⊔ v ⊔ w) where
    infixr 5 _+_
    field
      _+_ : ∀ a b → C a b
  open Plus ⦃ ... ⦄ public
  {-# DISPLAY Plus._+_ _ = _+_ #-}

  record Subtract : Type (u ⊔ v ⊔ w) where
    infixr 5 _-_
    field
      _-_ : ∀ a b → C a b
  open Subtract ⦃ ... ⦄ public
  {-# DISPLAY Subtract._-_ _ = _-_ #-}

  record Times : Type (u ⊔ v ⊔ w) where
    infixr 5 _×_
    field
      _×_ : ∀ a b → C a b
  open Times ⦃ ... ⦄ public
  {-# DISPLAY Times._×_ _ A B = A × B #-}

  record Asterisk : Type (u ⊔ v ⊔ w) where
    infixr 6 _*_
    field
      _*_ : ∀ a b → C a b
  open Asterisk ⦃ ... ⦄ public
  {-# DISPLAY Asterisk._*_ _ = _*_ #-}

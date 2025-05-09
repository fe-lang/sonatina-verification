```agda

{-# OPTIONS --safe --cubical-compatible #-}

module Trait.Cut where

open import Prim.Type

record Cut {u v w}
  (A : Type u)
  (B : A → Type v)
  (C : ∀ x → B x → Type w)
  : Typeω
  where
  infixr 40 _∘_ seq
  infixr 2 cut-syntax

  field
    seq : ∀ {x} (a : B x) → C x a
  {-# INLINE seq #-}

  _∘_ cut-syntax : ∀ x (a : B x) → C x a
  _∘_ x = seq {x}
  {-# INLINE _∘_ #-}

  cut-syntax x = seq {x}
  {-# INLINE cut-syntax #-}

  syntax cut-syntax x a b = x ⟩ a ≡ b

open Cut ⦃ ... ⦄  renaming ( seq to _∙_ ) public

{-# DISPLAY Cut.seq _ = _∙_ #-}
{-# DISPLAY Cut._∘_ _ = _∘_ #-}

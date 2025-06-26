```agda

{-# OPTIONS --safe --cubical-compatible #-}

module Meta.Cut.Type where

open import Prim.Type

record Cut {u v w} (A : Type u) (B : A → Type v) (C : ∀ x → B x → Type w) : Typeω
  where
  infixr 40 seq _∘_
  field
    seq : ∀ {x} (b : B x) → C x b
  {-# INLINE seq #-}

  _∘_ : ∀ g (f : B g) → C g f
  g ∘ f = seq {g} f
  {-# INLINE _∘_ #-}

open Cut ⦃ ... ⦄  renaming ( seq to _∙_ ) public

{-# DISPLAY Cut.seq _ = _∙_ #-}
{-# DISPLAY Cut._∘_ _ = _∘_ #-}

Hom-Cut : ∀ {u v} {Ob : Type u} (_~_ : Ob → Ob → Type v) → Typeω
Hom-Cut {Ob} _~_ = {y z : Ob} → Cut Ob (λ (x : Ob) → x ~ y) λ (x : Ob) _ → y ~ z → x ~ z

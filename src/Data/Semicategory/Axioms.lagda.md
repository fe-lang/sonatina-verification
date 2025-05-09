```agda
{-# OPTIONS --safe --erased-cubical #-}

open import Data.Semicategory.Type

module Data.Semicategory.Axioms {o h} (S : Semicategory o h) where

open import Prim.Type
open import Prim.Pi
open import Lib.Interval
open import Prim.Data.Sigma

open import Prim.Path
open import Prim.Equiv

open import Data.Semicategory.Iso S
open Semicategory S


```

Recall the definition of a Semicategory

record Semicategory o h : Type₊ (o ⊔ h) where
  infixr 40 _∘_
  field
    Ob : Type o
    Hom : Ob → Ob → Type h
    _⨾_ : ∀ {x y z} → Hom y z → Hom x y → Hom x z
    assoc : ∀ {w x y z} (f : Hom w x) (g : Hom x y) (h : Hom y z)
          → (h ∘ g) ∘ f ＝ h ∘ (g ∘ f)

```
record has-identity (x : Ob) : Type (o ⊔ h) where
  field
    idn : Hom x x
    idpt : idn ⨾ idn ＝ idn
    iso : is-iso idn

  open is-iso iso public

is-category : Type (o ⊔ h)
is-category = ∀ x → has-identity x

module is-category (p : is-category) where
  module _ (x : Ob) where open has-identity (p x) public

  idnr : ∀ {x y} (f : Hom x y) → f ⨾ idn y ＝ f
  idnr {x = x} {y = y} f =
    let module eq = is-equiv (invr y x)
        open eq renaming ( inv to cod )
    in
     f ⨾ idn y ＝⟨ sym (ap (_⨾ idn y) (retr f)) ⟩
     (cod f ⨾ idn y) ⨾ idn y ＝⟨ sym (assoc (cod f) (idn y) (idn y)) ⟩
     cod f ⨾ idn y ⨾ idn y ＝⟨ ap (cod f ⨾_) (idpt y) ⟩
     cod f ⨾ idn y ＝⟨ retr f ⟩
     refl

  idnl : ∀ {x y} (f : Hom x y) → idn x ⨾ f ＝ f
  idnl {x = x} {y = y} f =
    let module eq = is-equiv (invl x y)
        open eq renaming ( inv to dom )
    in
      idn x ⨾ f  ＝⟨ sym (ap (idn x ⨾_) (retr f)) ⟩
      idn x ⨾ idn x ⨾ dom f ＝⟨ assoc (idn x) (idn x) (dom f) ⟩
      (idn x ⨾ idn x) ⨾ dom f ＝⟨ ap (_⨾ dom f) (idpt x) ⟩
      idn x ⨾ dom f ＝⟨ retr f ⟩
      refl

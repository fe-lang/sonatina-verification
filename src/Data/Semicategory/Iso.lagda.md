```agda
{-# OPTIONS --safe --erased-cubical #-}

open import Data.Semicategory.Type

module Data.Semicategory.Iso {o h} (S : Semicategory o h) where

open import Prim.Type
open import Lib.Interval
open import Data.Sigma.Type

open import Prim.Path
open import Trait.Equiv

open Semicategory S

```

Recall the definition of a Semicategory

record Semicategory o h : Type₊ (o ⊔ h) where
  infixr 40 _∘_
  field
    Ob : Type o
    Hom : Ob → Ob → Type h
    _∘_ : ∀ {x y z} → Hom y z → Hom x y → Hom x z
    assoc : ∀ {w x y z} (f : Hom w x) (g : Hom x y) (h : Hom y z)
          → (h ∘ g) ∘ f ＝ h ∘ (g ∘ f)

```
is-left-inverse : {x y : Ob} → Hom x y → Type (o ⊔ h)
is-left-inverse {x} {y} f = (z : Ob) → is-equiv (λ (g : Hom y z) → f ⨾ g)

is-right-inverse : {x y : Ob} → Hom x y → Type (o ⊔ h)
is-right-inverse {x = x} g = (w : Ob) → is-equiv (λ (f : Hom w x) → f ⨾ g)

record is-iso {x y} (e : Hom x y) : Type (o ⊔ h) where
  field
    invl : is-left-inverse e
    invr : is-right-inverse e

  module invl {z : Ob} = is-equiv (invl z)
  module invr {w : Ob} = is-equiv (invr w)

open is-iso renaming ( invl to iso-invl; invr to iso-invr ) public

-- module _ {a b c} {f : Hom a b} {g : Hom b c} where
--   seq-is-iso : is-iso f → is-iso g → is-iso (f ⨾ g)
--   seq-is-iso (f-invl , f-invr) (g-invl , g-invr) .iso-invl z .eq-inv h =
--     let module f-invl {x} = is-equiv (f-invl x)
--         module g-invl {x} = is-equiv (g-invl x)
--         module f-invr {x} = is-equiv (f-invr x)
--         module g-invr {x} = is-equiv (g-invr x)
--     in g-invl.inv (f-invl.inv (f-invr.inv f)) ⨾ h
--   seq-is-iso (f-invl , f-invr) (g-invl , g-invr) .iso-invl z .eq-sec x = {!!}
--   seq-is-iso (f-invl , f-invr) (g-invl , g-invr) .iso-invl z .eq-retr = {!!}
--   seq-is-iso (f-invl , f-invr) (g-invl , g-invr) .iso-invl z .eq-adj = {!!}
--   seq-is-iso (f-invl , f-invr) (g-invl , g-invr) .iso-invr = {!!}

is-idempotent : ∀ {x} → Hom x x → Type h
is-idempotent f = f ⨾ f ＝ f

Iso : Ob → Ob → Type (o ⊔ h)
Iso x y = Σ f ∶ Hom x y , is-iso f

syntax Iso x y = x ≅ y

-- comp-iso : ∀ {x y z} → x ≅ y → y ≅ z → x ≅ z
-- comp-iso (f , f-iso) (g , g-iso) .fst = f ⨾ g
-- comp-iso (f , f-iso) (g , g-iso) .snd = seq-is-iso f-iso g-iso

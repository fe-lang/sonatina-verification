```agda
{-# OPTIONS --safe --erased-cubical #-}

module Data.Semicategory.Type where

open import Prim.Type
open import Lib.Pi using ( flip )
open import Prim.Path using ( _＝_; refl; sym )

record Semicategory o h : Type₊ (o ⊔ h) where
  infixr 40 _⨾_
  field
    Ob : Type o
    Hom : Ob → Ob → Type h
    _⨾_ : ∀ {x y z} → Hom x y → Hom y z → Hom x z
    assoc : ∀ {w x y z} (f : Hom w x) (g : Hom x y) (h : Hom y z)
          → f ⨾ (g ⨾ h) ＝ (f ⨾ g) ⨾ h

  op : Semicategory o h
  op .Ob = Ob
  op .Hom = flip Hom
  op ._⨾_ f g = g ⨾ f
  op .assoc f g h = sym (assoc h g f)

private module _ {o h} (S : Semicategory o h) where
  open Semicategory S

  op-op : Semicategory.op op ＝ S
  op-op = refl

semicategory : ∀ {o h} (ob : Type o) (hom : ob → ob → Type h)
             → (_⨾_ : ∀ {x y z} → hom x y → hom y z → hom x z)
             → (∀ {w x y z} (f : hom w x) (g : hom x y) (h : hom y z)
                  → f ⨾ (g ⨾ h) ＝ (f ⨾ g) ⨾ h)
             → Semicategory o h
semicategory ob hom _⨾_ assoc .Semicategory.Ob = ob
semicategory ob hom _⨾_ assoc .Semicategory.Hom = hom
semicategory ob hom _⨾_ assoc .Semicategory._⨾_ = _⨾_
semicategory ob hom _⨾_ assoc .Semicategory.assoc = assoc

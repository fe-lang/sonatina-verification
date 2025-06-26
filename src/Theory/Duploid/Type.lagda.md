```agda
{-# OPTIONS --safe --erased-cubical #-}

module Theory.Duploid.Type where

open import Prim.Type
open import Data.Pi using ( flip )

open import Data.Path.Type
open import Trait.Category.Type

record Lang o h : Type₊ (o ⊔ h) where
  field
    Ob : Type o
    _⊢_ : Ob → Ob → Type h
    cut : ∀ {A B C} → A ⊢ B → B ⊢ C → A ⊢ C
    has-idn : ∀ x → has-identity _⊢_ cut x

  private module idn (x : Ob) = has-identity (has-idn x)
  open idn public

  field
    idn-assocl : ∀ {A B} (f : A ⊢ B) → cut (idn A) (cut (idn A) f) ＝ cut (cut (idn A) (idn A)) f
    idn-assocr : ∀ {A B} (f : A ⊢ B) → cut (cut f (idn B)) (idn B) ＝ cut f (cut (idn B) (idn B))

  open is-category _⊢_ cut has-idn idn-assocl idn-assocr public

  -- op : Semicategory o h
  -- op .Ob = Ob
  -- op .Hom = flip Hom
  -- op ._⨾_ f g = g ⨾ f
  -- op .assoc f g h = sym (assoc h g f)

-- private module _ {o h} (S : Semicategory o h) where
--   open Semicategory S

--   op-op : Semicategory.op op ＝ S
--   op-op = refl

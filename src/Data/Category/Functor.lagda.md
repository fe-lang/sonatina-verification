```agda
{-# OPTIONS --safe --erased-cubical #-}

module Data.Category.Functor where

open import Prim.Prelude
open import Data.Path.Type
open import Data.Category.Type

module _ {o o' h h'} (C : Category o h) (D : Category o' h') where
  private
    module C = Category C
    module D = Category D

  record Functor : Type (o ⊔ o' ⊔ h ⊔ h') where
    field
      F₀ : C.Ob → D.Ob
      F₁ : ∀ {x y} → C.Hom x y → D.Hom (F₀ x) (F₀ y)
      idn : ∀ x → F₁ (C.idn x) ＝ D.idn (F₀ x)
      hom : ∀ {x y z} (g : C.Hom y z) (f : C.Hom x y)
          → F₁ (f ∙ g) ＝ F₁ f ∙ F₁ g

module _ {o o' h h'} (C : Category o h) (D : Category o' h') where
  private module C = Category C
          module D = Category D

  Contravariant-functor : Type (o ⊔ o' ⊔ h ⊔ h')
  Contravariant-functor = Functor C.op D

module _ {o₁ o₂ o₃ h₁ h₂ h₃}
  {C : Category o₁ h₁}
  {D : Category o₂ h₂}
  {E : Category o₃ h₃}
  where
  private module C = Category C
          module D = Category D
          module E = Category E

  F-comp : Functor C D → Functor D E → Functor C E
  F-comp F G = FG
    where
    module F = Functor F
    module G = Functor G

    FG : Functor C E
    FG .Functor.F₀ x = G.F₀ (F.F₀ x)
    FG .Functor.F₁ f = G.F₁ (F.F₁ f)
    FG .Functor.idn x = ap G.F₁ (F.idn x) ∙ G.idn (F.F₀ x)
    FG .Functor.hom g f = ap G.F₁ (F.hom g f) ∙ G.hom (F.F₁ g) (F.F₁ f)

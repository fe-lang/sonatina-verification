```agda
{-# OPTIONS --safe --erased-cubical #-}

open import Theory.Duploid.Type
module Theory.Duploid.Properties {o h} (L : Lang o h) where

open import Lib.Base
open import Data.Sum.Type
open import HData.Trunc.Prop

open Lang L

private ℓ = o ⊔ h

module _ {A B : Ob} (f : A ⊢ B) where
  is-thunkable : Type ℓ
  is-thunkable = ∀ {C D} (g : B ⊢ C) (h : C ⊢ D)
               → cut (cut f g) h ＝ cut f (cut g h)

  is-linear : Type ℓ
  is-linear = ∀ {U V} (g : V ⊢ A) (h : U ⊢ V)
            → cut (cut h g) f ＝ cut h (cut g f)

idn-linear : ∀ A → is-linear (idn A)
idn-linear A g h =
  cut (cut h g) (idn A) ＝⟨ idnr (cut h g) ⟩
  cut h g               ＝⟨ ap (cut h) (sym (idnr g)) ∣
  {!!} ∎

idn-thunkable : ∀ A → is-thunkable (idn A)
idn-thunkable A g h =
  {!!} ＝⟨ ap (λ f → cut f h) (idnl g) ⟩
  cut g h ＝⟨ sym (idnl (cut g h)) ⟩
  refl

is-positive : ∀ A → Type ℓ
is-positive A = (B : Ob) (f : A ⊢ B) → is-linear f

is-negative : ∀ A → Type ℓ
is-negative A = (B : Ob) (f : B ⊢ A) → is-thunkable f

is-polarized : ∀ A → Type ℓ
is-polarized A = ∥ is-positive A ⊎ is-negative A ∥ 

is-left-inverse : ∀ {x y} → x ⊢ y → Type (o ⊔ h)
is-left-inverse {x} {y} f = (z : Ob) → is-equiv (λ (g : y ⊢ z) → cut f g)

is-right-inverse : ∀ {x y} → x ⊢ y → Type (o ⊔ h)
is-right-inverse {x = x} g = (w : Ob) → is-equiv (λ (f : w ⊢ x) → cut f g)

record is-iso {x y} (e : x ⊢ y) : Type (o ⊔ h) where
  field
    invl : is-left-inverse e
    invr : is-right-inverse e

open is-iso renaming ( invl to iso-invl; invr to iso-invr ) public

Iso : Ob → Ob → Type (o ⊔ h)
Iso x y = Σ f ∶ x ⊢ y , is-iso f

is-thunkable-iso : ∀ {A B} → A ⊢ B → Type (o ⊔ h)
is-thunkable-iso f = is-thunkable f × is-iso f

is-linear-iso : ∀ {A B} → A ⊢ B → Type (o ⊔ h)
is-linear-iso f = is-linear f × is-iso f

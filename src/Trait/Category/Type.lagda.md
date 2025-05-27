```agda
{-# OPTIONS --safe --erased-cubical #-}

module Trait.Category.Type where

open import Prim.Type
open import Data.Path.Type
open import Trait.Equiv using ( is-equiv )
open import Data.Path.Reasoning

module _ {o h} {Ob : Type o}
  (R : Ob → Ob → Type h)
  (_⨾_ : ∀ {x y z} → R x y → R y z → R x z)
  where

  record has-identity (x : Ob) : Type (o ⊔ h) where
    field
      idn : R x x
      idn-idpt : idn ⨾ idn ＝ idn
      idn-sec : (y : Ob) → is-equiv (λ (g : R x y) → idn ⨾ g)
      idn-retr : (w : Ob) → is-equiv (λ (f : R w x) → f ⨾ idn)

  is-category : Type (o ⊔ h)
  is-category = ∀ x → has-identity x

  module is-category (C : is-category)
    (let module C x = has-identity (C x))
    (idn-assocl : ∀ {x y} (f : R x y)
                → C.idn x ⨾ (C.idn x ⨾ f) ＝ (C.idn x ⨾ C.idn x) ⨾ f)
    (idn-assocr : ∀ {x y} (f : R x y)
                → (f ⨾ C.idn y) ⨾ C.idn y ＝ f ⨾ (C.idn y ⨾ C.idn y))
    where
    private module s {x y} = is-equiv (C.idn-sec x y)
    private module r {x y} = is-equiv (C.idn-retr x y)

    idnr : ∀ {x y} (f : R x y) → f ⨾ (C.idn y) ＝ f
    idnr {x = x} {y = y} f =
       f ⨾ C.idn y
         ＝⟨ sym (ap (_⨾ C.idn y) (retr f)) ⟩
       ((cod f) ⨾ C.idn y) ⨾ C.idn y
         ＝⟨ idn-assocr (cod f) ⟩
       (cod f) ⨾ (C.idn y ⨾ C.idn y)
         ＝⟨ ap (cod f ⨾_) (C.idn-idpt y) ⟩
       cod f ⨾ C.idn y
         ＝⟨ retr f ∣
       f ∎ where open r renaming ( inv to cod )

    idnl : ∀ {x y} (f : R x y) → C.idn x ⨾ f ＝ f
    idnl {x = x} {y = y} f =
        C.idn x ⨾ f
          ＝⟨ sym (ap (C.idn x ⨾_) (retr f)) ⟩
        C.idn x ⨾ (C.idn x ⨾ (dom f))
          ＝⟨ idn-assocl (dom f) ⟩
       (C.idn x ⨾ C.idn x) ⨾ dom f
          ＝⟨ ap (_⨾ dom f) (C.idn-idpt x) ⟩
        C.idn x ⨾ dom f
          ＝⟨ retr f ∣
        f ∎ where open s renaming ( inv to dom )

```agda

{-# OPTIONS --safe --erased-cubical #-}

module Data.Category.Family where

open import Prim.Type
open import Prim.Pi
open import Prim.Data.Path
open import Prim.Data.Sigma
open import Prim.Equiv
open import Prim.Kan using (path-reasoning-syntax)
open import Data.Category.Type
open import Trait.Category.Type

module _ {o h f} (C : Category o h)
  (let module C = Category C)
  (Fam : C.Ob → Type f)
  (_>>>_ : ∀ {x y} → C.Hom y x → Fam x → Fam y)
  where
  record has-fam-category (x : C.Ob) : Type (o ⊔ h ⊔ f) where
    field
      dep-idn : (w : C.Ob) → is-equiv (λ (Λ : Fam w) → C.idn w >>> Λ)
      dep-assocl : {w x y : C.Ob} (f : C.Hom y w) (g : C.Hom x y)
                → is-equiv (λ (Λ : Fam w) → ((C.seq g f) >>> Λ))
      dep-assocr : {w x y : C.Ob} (f : C.Hom y w) (g : C.Hom x y)
                 → is-equiv (λ (Λ : Fam w) → g >>> (f >>> Λ))


  is-fam-category : Type (o ⊔ h ⊔ f)
  is-fam-category = ∀ x → has-fam-category x

record Fam-category {o h} f (𝓒 : Category o h) : Type₊ (o ⊔ h ⊔ f) where
  private module C = Category 𝓒
  field
    Fam : C.Ob → Type f
    fseq : ∀ {x y} → C.Hom y x → Fam x → Fam y
    is-cat-fam : is-fam-category 𝓒 Fam fseq

  private _>>_ = fseq

  module _ (x : C.Ob) where open has-fam-category (is-cat-fam x) public

  idnd : ∀ {x} (Λ : Fam x) → C.idn x >> Λ ＝ Λ
  idnd {x} Λ = 
    (C.idn x >> Λ) ＝⟨ {!!} ⟩
    {!!} ＝⟨ {!!} ⟩
    {!!} ∎
    where
    module idnd {x y} = is-equiv (dep-idn x y)
    module assocl {x y z} {f : C.Hom z y} {g : C.Hom y x} =
      is-equiv (dep-assocl x g f)
    module assocr {x y z} {f : C.Hom z y} {g : C.Hom y x} =
      is-equiv (dep-assocr x g f)

  -- idnr : ∀ {x y} (f : Hom x y) → seq f (idn y) ＝ f
  -- idnr {x = x} {y = y} f =
  --   let module eq = is-equiv (idn-retr y x)
  --       open eq renaming ( inv to cod )
  --   in
  --    seq f (idn y)
  --      ＝⟨ sym (ap (λ f → seq f (idn y)) (eq.retr f)) ⟩
  --    seq (seq (cod f) (idn y)) (idn y)
  --      ＝⟨ sym (assoc (cod f) (idn y) (idn y)) ⟩
  --    seq (cod f) (seq (idn y) (idn y))
  --      ＝⟨ ap (seq (cod f)) (idn-idpt y) ⟩
  --    seq (cod f) (idn y)
  --      ＝⟨ eq.retr f ⟩
  --    refl

  -- idnl : ∀ {x y} (f : Hom x y) → seq (idn x) f ＝ f
  -- idnl {x = x} {y = y} f =
  --   let module eq = is-equiv (idn-sec x y)
  --       open eq renaming ( inv to dom )
  --   in
  --     seq (idn x) f
  --       ＝⟨ sym (ap (seq (idn x)) (eq.retr f)) ⟩
  --     seq (idn x) (seq (idn x) (dom f))
  --       ＝⟨ assoc (idn x) (idn x) (dom f) ⟩
  --     seq (seq (idn x) (idn x)) (dom f)
  --       ＝⟨ ap (λ h → seq h (dom f)) (idn-idpt x) ⟩
  --     seq (idn x) (dom f)
  --       ＝⟨ eq.retr f ⟩
  --     refl

  -- op : Category o h
  -- op .Ob = Ob
  -- op .Hom = flip Hom
  -- op .seq = flip seq
  -- op .assoc f g h = sym (assoc h g f)
  -- op .is-cat x .has-identity.idn = idn x
  -- op .is-cat x .has-identity.idn-idpt = idn-idpt x
  -- op .is-cat x .has-identity.idn-sec y = idn-retr x y
  -- op .is-cat x .has-identity.idn-retr y = idn-sec x y

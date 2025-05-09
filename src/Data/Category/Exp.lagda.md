```agda
{-# OPTIONS --safe --erased-cubical #-}

module Data.Category.Exp where

open import Prim.Type
open import Prim.Pi
open import Prim.Path
open import Prim.Data.Sigma

open import Prim.Equiv
open import Lib.Equiv.Identity

-- record Category o h : Type₊ (o ⊔ h) where
--   field
--     Ob : I → Type o
--     Hom : Ob i0 → Ob i1 → Type h
--     precomp : ∀ {x : Ob i0} {y : Ob i1} {z : Ob i1}
--             → Hom x y → Hom x z
--     seq : ∀ {x y z} → Hom x y → Hom y z → Hom x z
--     -- assoc : ∀ {i w x y z} (f : Hom {i} w x) (g : Hom x y) (h : Hom y z)
--     --       → seq f (seq g h) ＝ seq (seq f g) h
--     -- is-cat : (i : I) → is-category (Hom {i}) seq

  --module _ (x : Ob) where open has-identity (is-cat x) public

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

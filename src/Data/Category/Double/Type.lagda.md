```agda
{-# OPTIONS --safe --erased-cubical #-}

module Data.Category.Double.Type where

open import Prim.Type
open import Lib.Interval
open import Prim.Path
open import Prim.Equiv

record has-identity {o h} {Ob : Type o}
  (_⇒_ : Ob → Ob → Type h)
  (_⨾_ : ∀ {x y z} → x ⇒ y → y ⇒ z → x ⇒ z) (x : Ob)
  : Type (o ⊔ h)
  where
  field
    idn : x ⇒ x
    idn-idpt : idn ⨾ idn ＝ idn
    idn-invl : (y : Ob) → is-equiv (λ (g : x ⇒ y) → idn ⨾ g)
    idn-invr : (w : Ob) → is-equiv (λ (f : w ⇒ x) → f ⨾ idn)

record has-dep-identity {o h} (Ob : I → Type o)
  (R : ∀ {i j} → Ob i → Ob j → Type h)
  {i : I} (x : Ob i)
  (_⨾_ : ∀ {i j} {x : Ob i} {y : Ob j} {z : Ob i}
       → R x y → R y z → R x z)
  : Type (o ⊔ h)
  where
  field
    idn : R x x
    idn-idpt : idn ⨾ idn ＝ idn
    idn-invl : (y : Ob i) → is-equiv (λ (g : R x y) → idn ⨾ g)
    idn-invr : (w : Ob i) → is-equiv (λ (f : R w x) → f ⨾ idn)



record DblCategory o h₁ h₂ : Type₊ (o ⊔ h₁ ⊔ h₂) where
  field
    Ob : I → Type o
    Homv : ∀ {i j} → Ob i → Ob j → Type h₁
    _⨾t_ : ∀ {i j} {a : Ob (~ i)} {b : Ob (i ∧ j)} {c : Ob (i ∨ j)} → Homv a b → Homv b c → Homv a c
    idn : ∀ {i} (x : Ob i) → has-dep-identity Ob Homv {i} x (_⨾t_ {i ∨ {!~ i!}})

  -- ob~ : ∀ {i} {x : Ob (~ i)} (a : Ob i) → Homt a x → Ob (~ i)
  -- ob~ a h = {!!}

    -- idn₀ : ∀ x → has-identity Homt _⨾v_ x
    -- Homs : ∀ {a b x} → Homt a x → Homt b x → Type h₂
    -- _⨾s_ : ∀ {a b c d} {p }


    
    -- --Homh : ∀ {a b c d} → Homv a b d → Homv a c d → Type h₂
    -- _⨾h_ : ∀ {a b c d e f}
    --      → {p : Homv a b d} {q : Homv a c d}
    --      → {r : Homv c d f} {s : Homv c e f}
    --     → Homh p q → Homh q {!!} → Homh {!!} {!!}


```
Sq : (p : a00 ⇒ a10) → (q : a00 ⇒ a01) → (a10 ⇒ a11 → a01 ⇒ a11 → Type h)

p q u → (tgt p ⇒ u → tgt q ⇒ u → Type h)

  -- op : DblCategory o h
  -- op .base = Semicategory.op base
  -- op .is-cat x .has-identity.idn = idn x
  -- op .is-cat x .has-identity.idpt = idpt x
  -- op .is-cat x .has-identity.iso =
  --   let open Data.Semicategory.Iso base
  --   in record { invl = λ z → invr x z ; invr = λ w → invl x w }

-- _[_,_] : ∀ {o h} (C : Category o h)
--        → (let module C = Category C)
--        → C.Ob → C.Ob → Type h
-- C [ x , y ] = Category.Hom C x y
-- {-# DISPLAY Category.Hom C x y = C [ x , y ] #-}

-- _[_⨾_] : ∀ {o h} (C : Category o h)
--        → (let module C = Category C)
--        → ∀ {x y z} → C.Hom x y → C.Hom y z → C.Hom x z
-- C [ f ⨾ g ] = Category._⨾_ C f g
-- {-# DISPLAY Category._⨾_ C f g = C [ f ⨾ g ] #-}

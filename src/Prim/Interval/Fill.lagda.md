Elementary fillers for path squares

```agda

{-# OPTIONS --safe --erased-cubical #-}

module Prim.Interval.Fill where

open import Prim.Type
open import Prim.Interval.Core
open import Prim.Data.Path
open import Prim.Interval.Kan renaming (path-comp to infixr 40 _∙_)

open Square

module _ {ℓ} {A : Type ℓ} where
  neutral-square : {x y z : A} (p : x ＝ y) (q : y ＝ z) → p ⌞ p ⌟ q ⇒ q
  neutral-square {x = x} {y} {z} p q j i =
    hfill (∂ j ∨ i) i λ where
      k (j = i0) → p (i ∨ k)
      k (j = i1) → q (i ∧ k)
      k (i = i1) → q (j ∧ k)
      k (k = i0) → p (i ∨ j)

  -- https://q.uiver.app/#q=WzAsMjEsWzIsMiwieCAiXSxbMiw0LCJ5Il0sWzQsMiwieSJdLFs0LDQsInkiXSxbNCwwLCJ5Il0sWzYsMiwieSJdLFsyLDYsInkiXSxbNCw2LCJ6Il0sWzQsOCwieSJdLFs2LDQsInoiXSxbMCwyLCJ5Il0sWzAsNCwieSJdLFszLDUsImk9aTAiXSxbMyw3LCJrPWkwIl0sWzIsOCwieSJdLFs0LDEwLCJcXGJ1bGxldCJdLFsyLDAsInkiXSxbMSwzLCJqPWkwIl0sWzUsMywiaj1pMSJdLFszLDEsImk9aTEiXSxbMywzLCJrPWkxIl0sWzUsMl0sWzYsMSwiIiwxLHsic3R5bGUiOnsiYm9keSI6eyJuYW1lIjoiZGFzaGVkIn19fV0sWzcsMywicVxcIFxcbmVnIGsiLDFdLFs2LDcsInFcXCBqIiwxXSxbNyw4LCJxXFwgXFxuZWcgaSIsMV0sWzksMywicVxcIFxcbmVnIGsiLDFdLFswLDIsInBcXCBqIiwxXSxbMSwzLCIiLDEseyJzdHlsZSI6eyJib2R5Ijp7Im5hbWUiOiJkYXNoZWQifX19XSxbOSw1LCJxXFwgXFxuZWcgaSIsMV0sWzMsMiwiIiwxLHsic3R5bGUiOnsiYm9keSI6eyJuYW1lIjoiZGFzaGVkIn19fV0sWzEsMCwicFxcIFxcbmVnIGkiLDFdLFsxMSwxMCwiIiwxLHsic3R5bGUiOnsiYm9keSI6eyJuYW1lIjoiZGFzaGVkIn19fV0sWzQsMiwiIiwxLHsic3R5bGUiOnsiYm9keSI6eyJuYW1lIjoiZGFzaGVkIn19fV0sWzEwLDAsInBcXCBcXG5lZyBrIiwxXSxbMTEsMSwiIiwxLHsic3R5bGUiOnsiYm9keSI6eyJuYW1lIjoiZGFzaGVkIn19fV0sWzE0LDgsIiIsMSx7InN0eWxlIjp7ImJvZHkiOnsibmFtZSI6ImRhc2hlZCJ9fX1dLFsxNiwwLCJwXFwgXFxuZWcgayIsMV0sWzE2LDQsIiIsMSx7InN0eWxlIjp7ImJvZHkiOnsibmFtZSI6ImRhc2hlZCJ9fX1dLFs2LDE0LCIiLDEseyJzdHlsZSI6eyJib2R5Ijp7Im5hbWUiOiJkYXNoZWQifX19XSxbMzUsMjIsIiIsMSx7InNob3J0ZW4iOnsic291cmNlIjoyMCwidGFyZ2V0IjoyMH0sInN0eWxlIjp7ImhlYWQiOnsibmFtZSI6Im5vbmUifX19XSxbMzMsMjEsIiIsMSx7InNob3J0ZW4iOnsic291cmNlIjoyMCwidGFyZ2V0IjoyMH0sInN0eWxlIjp7ImhlYWQiOnsibmFtZSI6Im5vbmUifX19XSxbMzQsMzcsIiIsMSx7InNob3J0ZW4iOnsic291cmNlIjoyMCwidGFyZ2V0IjoyMH0sInN0eWxlIjp7ImhlYWQiOnsibmFtZSI6Im5vbmUifX19XSxbMjYsMjMsIiIsMSx7InNob3J0ZW4iOnsic291cmNlIjoyMCwidGFyZ2V0IjoyMH0sInN0eWxlIjp7ImhlYWQiOnsibmFtZSI6Im5vbmUifX19XV0=
  sym-square : {x y z : A} (p : x ＝ y) (q : y ＝ z) → sym p ⌞ q ⌟ sym q ⇒ p
  sym-square {x = x} {y} {z} p q = vsym (neutral-square p q)

  -- When the precomposed or postcomposed edges are a homotopy, we may
  -- fill a square using any path that composes with the homotopical paths,
  -- hence these are whiskering operations.
  sq-rwhisker : {x y z : A} (p q : x ＝ y) (r : y ＝ z)
              → p ＝ q → p ⌞ q ⌟ r ⇒ r
  sq-rwhisker p q r H i j = hcomp (∂ i ∨ ∂ j) λ where
    k (i = i0) → p j
    k (i = i1) → neutral-square q r j k
    k (j = i0) → q (i ∧ k)
    k (j = i1) → r (i ∧ k)
    k (k = i0) → H i j

  sq-lwhisker : {x y z : A} (p : x ＝ y) (q r : y ＝ z)
              → q ＝ r → p ⌞ p ⌟ q ⇒ r
  sq-lwhisker p q r H = sflip (sq-rwhisker (sym q) (sym r) (sym p) (vsym H))

```

Squares involving three variables have a degenerate face, hence
they are triangles up to homotopy. We can read transformations of
these degenerate squares as transporting the refl term along one of
the paths, so from reflexivity at x to y, or y to z, and so on.
```

module tri {ℓ} {A : Type ℓ} {x y z : A} (p : x ＝ y) (q : y ＝ z) (r : x ＝ z)
  (sq : erefl x ⌞ p ⌟ q ⇒ r)
  where
  by-pre : erefl y ⌞ sym p ⌟ r ⇒ q
  by-pre i j = hcomp (∂ i ∨ ∂ j) λ where
    k (i = i0) → p (j ∨ k)
    k (i = i1) → r j
    k (j = i0) → p (~ i ∧ k)
    k (j = i1) → q i
    k (k = i0) → sq j i
  {-# INLINE by-pre #-}
    
  by-comp : erefl z ⌞ sym r ⌟ p ⇒ sym q
  by-comp i j = hcomp (∂ i ∨ ∂ j) λ where
    k (i = i0) → r (j ∨ k)
    k (i = i1) → p j
    k (j = i0) → r (~ i ∧ k)
    k (j = i1) → q (~ i)
    k (k = i0) → sq j (~ i)
  {-# INLINE by-comp #-}

module _ {ℓ} {A : Type ℓ} {x y z : A} (p : x ＝ y) (q : y ＝ z) where
  path-lfiller : erefl x ⌞ p ⌟ q  ⇒ p ∙ q
  path-lfiller = path-filler refl p q

  -- These are helpers for making a square center or right refl to our
  -- canonical single dimensional composition operation
  path-cfiller : sym p ⌞ erefl y ⌟ q  ⇒ (p ∙ q)
  path-cfiller = transpose (tri.by-pre p q (p ∙ q) path-lfiller)

  path-rfiller : sym p ⌞ q ⌟ erefl z  ⇒ (p ∙ q)
  path-rfiller = hsym (tri.by-comp (sym p) (p ∙ q) q (transpose path-cfiller))

module _ {ℓ} {A : Type ℓ} where
  path-idpt : (x : A) → refl ∙ refl ＝ refl {x = x}
  path-idpt x i j = hcomp (∂ j ∨ i) (λ _ _ → x)

  path-invr : {x y : A} (p : x ＝ y) → p ∙ sym p ＝ erefl x
  path-invr {x = x} p i j = hcomp (∂ j ∨ i) λ where
    k (j = i0) → x
    k (j = i1) → p (~ i ∧ ~ k)
    k (i = i1) → x
    k (k = i0) → p (~ i ∧ j)

  path-invl : {x y : A} (p : x ＝ y) → (sym p) ∙ p ＝ erefl y
  path-invl p = path-invr (sym p)

  path-idnr : {x y : A} (p : x ＝ y) → p ∙ refl ＝ p
  path-idnr {x} {y} p = rrotate (path-lfiller p refl)

  path-idnl : {x y : A} (p : x ＝ y) → refl ∙ p ＝ p
  path-idnl {x} {y} p = rrotate (path-rfiller refl p)

  path-assoc : {w x y z : A} (p : w ＝ x) (q : x ＝ y) (r : y ＝ z)
             → p ∙ (q ∙ r) ＝ (p ∙ q) ∙ r
  path-assoc p q r i =
     transpose (path-lfiller p q) i ∙ rrotate (path-rfiller q r) i

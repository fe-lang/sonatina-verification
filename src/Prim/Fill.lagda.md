```agda
{-# OPTIONS --safe --erased-cubical #-}

module Prim.Fill where

open import Prim.Type
open import Prim.Cubical
open import Prim.Data.Path
open import Prim.Kan

open Square

module _ {ℓ} {A : Type ℓ} where
  hcomp-fill : {w x y z : A} (p : x ＝ w) (q : x ＝ y) (r : y ＝ z)
            → p ⌞ q ⌟ r ⇒ (p ⌞ q ⌟ r)
  hcomp-fill p q r i j = hfill (∂ i) j (path-faces p q r i)

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

  -- For squares involving three interval variables (i.e with a degenerate face)
  -- there are three transformations of a square corresponding to deformations
  -- that transport the refl term along the paths.
  sq-refl-top : {x y z : A} (p : x ＝ y) (q : x ＝ z) (r : z ＝ y)
               → p ⌞ q ⌟ r ⇒ erefl y
               → q ⌞ p ⌟ sym r ⇒ erefl z
  sq-refl-top p q r sq i j = hcomp (∂ i ∨ ∂ j) λ where
    k (i = i0) → q j
    k (i = i1) → r (~ j ∨ ~ k)
    k (j = i0) → p i
    k (j = i1) → r (i ∧ ~ k)
    k (k = i0) → sq j i

  sq-refl-bottom : {x y z : A} (p : x ＝ y) (q : x ＝ z) (r : y ＝ z)
               → p ⌞ erefl x ⌟ q ⇒ r
               → sym p ⌞ erefl y ⌟ r ⇒ q
  sq-refl-bottom p q r sq i j = hcomp (∂ i ∨ ∂ j) λ where
    k (i = i0) → p (~ j ∧ k)
    k (i = i1) → r j
    k (j = i0) → p (i ∨ k)
    k (j = i1) → q i
    k (k = i0) → sq j i

  sq-refl-left  : {x y z : A} (p : x ＝ y) (q : y ＝ z) (r : x ＝ z)
                → erefl x ⌞ p ⌟ q ⇒ r
                → erefl y ⌞ sym p ⌟ r ⇒ q
  sq-refl-left p q r sq i j = hcomp (∂ i ∨ ∂ j) λ where
    k (i = i0) → p (j ∨ k)
    k (i = i1) → r j
    k (j = i0) → p (~ i ∧ k)
    k (j = i1) → q i
    k (k = i0) → sq j i

  sq-refl-right  : {x y z : A} (p : x ＝ y) (q : x ＝ z) (r : y ＝ z)
                → p ⌞ q ⌟ erefl z ⇒ r
                → q ⌞ p ⌟ erefl y ⇒ sym r
  sq-refl-right p q r sq i j = hcomp (∂ i ∨ ∂ j) λ where
    k (i = i0) → q j
    k (i = i1) → r (j ∧ ~ k)
    k (j = i0) → p i
    k (j = i1) → r (~ i ∨ ~ k)
    k (k = i0) → sq j i

  sq-lswap : {x y z : A} (p : x ＝ y) (q : y ＝ z) (r : x ＝ z)
           → erefl x ⌞ p ⌟ q ⇒ r
           → r ⌞ p ⌟ q ⇒ erefl z
  sq-lswap p q r sq i j = hcomp (∂ i ∨ ∂ j) λ where
    k (i = i0) → r (j ∧ k)
    k (i = i1) → q j
    k (j = i0) → p i
    k (j = i1) → r (i ∨ k)
    k (k = i0) → sq i j

  -- When the precomposed or postcomposed edges are a homotopy, we may
  -- fill a square using any path that composes with the homotopical paths,
  -- hence these are whiskering operations.
  sq-lwhisker : {x y z : A} (p : x ＝ y) (q r : y ＝ z)
              → q ＝ r → p ⌞ p ⌟ q ⇒ r
  sq-lwhisker p q r H i j = hcomp (∂ i ∨ ∂ j) λ where
    k (i = i0) → p (j ∨ ~ k)
    k (i = i1) → q (j ∨ ~ k)
    k (j = i0) → neutral-square p q (~ k) i
    k (j = i1) → r i
    k (k = i0) → H j i

  sq-rwhisker : {x y z : A} (p q : x ＝ y) (r : y ＝ z)
              → p ＝ q → p ⌞ q ⌟ r ⇒ r
  sq-rwhisker p q r H i j = hcomp (∂ i ∨ ∂ j) λ where
    k (i = i0) → p j
    k (i = i1) → neutral-square q r j k
    k (j = i0) → q (i ∧ k)
    k (j = i1) → r (i ∧ k)
    k (k = i0) → H i j

  hcomp-crefl : {x y z : A} (p : x ＝ y) (q : y ＝ z)
              → sym p ⌞ refl ⌟ q ⇒ (refl ⌞ p ⌟ q)
  hcomp-crefl {y = y} p q i j =
    hfill (∂ i) j λ where
      k (i = i0) → p (~ j ∧ ~ k)
      k (i = i1) → q (j ∧ k)
      k (k = i0) → p (i ∨ ~ j)

  hcomp-rrefl : {x y z : A} (p : x ＝ y) (q : y ＝ z)
              → sym p ⌞ q ⌟ refl ⇒ (refl ⌞ p ⌟ q)
  hcomp-rrefl p q i j =
    hcomp (∂ i ∨ ~ j) λ where
      k (i = i0) → p (~ j ∧ k)
      k (i = i1) → q k
      k (j = i0) → sym-square p q i (~ k)
      k (k = i0) → p i

  hcomp-lrefl : {x y z : A} (p : x ＝ y) (q : y ＝ z)
             → refl ⌞ sym p ⌟ (refl ⌞ p ⌟ q) ⇒ q
  hcomp-lrefl {x = x} {y} {z} p q i j =
    hcomp (∂ j ∨ ~ i) λ where
      k (j = i0) → p (~ i)
      k (j = i1) → q (i ∧ k)
      k (i = i0) → y
      k (k = i0) → p (~ i ∨ j)

  path-idpt : (x : A) → path-comp refl refl ＝ refl {x = x}
  path-idpt x i j = hcomp (∂ j ∨ i) (λ _ _ → x)

  path-invr : {x y : A} (p : x ＝ y) → path-comp p (sym p) ＝ refl
  path-invr {x = x} {y = y} p j i = hcomp (∂ i ∨ j) λ where
    k (i = i0) → x
    k (i = i1) → p (~ j ∧ ~ k)
    k (j = i1) → x
    k (k = i0) → p (i ∧ ~ j)

  path-invl : {x y : A} (p : x ＝ y) → path-comp (sym p) p ＝ refl
  path-invl p = path-invr (sym p)

  path-idnl : {x y : A} (p : x ＝ y) → path-comp refl p ＝ p
  path-idnl {x} {y} p i j = hcomp (∂ j ∨ i) λ where
    k (j = i0) → x
    k (j = i1) → p (i ∨ k)
    k (i = i1) → p j
    k (k = i0) → p (i ∧ j)

  path-idnr : {x y : A} (p : x ＝ y) → path-comp p refl ＝ p
  path-idnr {x} {y} p i j = hcomp (∂ j ∨ i) λ where
    k (j = i0) → x
    k (j = i1) → y
    k (i = i1) → p j
    k (k = i0) → p j

  path-assoc : {w x y z : A} (p : w ＝ x) (q : x ＝ y) (r : y ＝ z)
             → path-comp p (path-comp q r) ＝ path-comp (path-comp p q) r
  path-assoc p q r i =
    path-comp (transpose (hcomp-fill refl p q) i) (rrotate (hcomp-rrefl q r) i)
    where open Square

```agda
{-# OPTIONS --safe --erased-cubical #-}

module Data.Path.Square where

open import Prim.Type
open import Prim.Interval
open import Prim.Kan
open import Meta.Cut

open import Data.Sigma.Type
open import Data.Path.Base
open import Data.Path.Base

Square : ∀ {ℓ} {A : Type ℓ}
       → {a00 a01 : A} (p : a00 ＝ a01)
       → {a10 : A} (q : a00 ＝ a10)
       → {a11 : A} (r : a10 ＝ a11) (s : a01 ＝ a11)
       → Type ℓ
Square p q r s = PathP (λ i → q i ＝ s i) p r
syntax Square p q r s = p ⌞ q ⌟ r ⇒ s

SquareP : ∀ {ℓ} (A : I → I → Type ℓ)
        → {a00 : A i0 i0} {a01 : A i0 i1}
        → {a10 : A i1 i0} {a11 : A i1 i1}
        → PathP (λ j → A i0 j) a00 a01
        → PathP (λ i → A i i0) a00 a10
        → PathP (λ j → A i1 j) a10 a11
        → PathP (λ i → A i i1) a01 a11
        → Type ℓ
SquareP A p q r s = PathP (λ i → PathP (λ j → A i j) (q i) (s i)) p r

module _ {ℓ} {A : Type ℓ} {a00 a01 a10 a11 : A}
  {p : a00 ＝ a01} {q : a00 ＝ a10} {r : a10 ＝ a11} {s : a01 ＝ a11}
  where
  hsym : Square p q r s → Square r (sym q) p (sym s)
  hsym α i j = α (~ i) j
  {-# INLINE hsym #-}

  vsym : Square p q r s → Square (sym p) s (sym r) q
  vsym α i j = α i (~ j)
  {-# INLINE vsym #-}

  lrotate : Square p q r s → Square (sym q) r (sym s) p
  lrotate α i j = α (~ j) i
  {-# INLINE lrotate #-}

  rrotate : Square p q r s → Square s (sym p) q (sym r)
  rrotate α i j = α j (~ i)
  {-# INLINE rrotate #-}

  sflip : Square p q r s → Square (sym r) (sym s) (sym p) (sym q)
  sflip α i j = α (~ i) (~ j)
  {-# INLINE sflip #-}

  transpose : Square p q r s → Square q p s r
  transpose α i j = α j i
  {-# INLINE transpose #-}

  itranspose : Square p q r s → Square (sym s) (sym r) (sym q) (sym p)
  itranspose α i j = α (~ j) (~ i)
  {-# INLINE itranspose #-}

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

path-filler : ∀ {ℓ} {A : Type ℓ}  {w x y z : A}
            → (p : x ＝ w) (q : x ＝ y) (r : y ＝ z)
            → p ⌞ q ⌟ r ⇒ lid p q r
path-filler p q r i j = hfill (∂ i) j (path-sys p q r i)

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

cone : ∀ {ℓ} {A : Type ℓ} {x y z : A} (q : y ＝ z) (r : x ＝ z)
     → Square q (q ∙ sym r) r refl
cone {z = z} q r i j = hcomp (∂ i ∨ j) λ where
  k (i = i0) → q j
  k (k = i0) → q (i ∨ j)
  k (i = i1) → r (j ∨ ~ k)
  k (j = i1) → z

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

Path-filler : ∀ {ℓ} {A : Type ℓ} {w x y z : A}
            → (p : x ＝ w) (q : x ＝ y) (r : y ＝ z) → Type ℓ
Path-filler {w = w} {z = z} p q r =
  Σ s ∶ (w ＝ z) , Square p q r s

module Path-filler {ℓ} {A : Type ℓ} {w x y z : A}
  (p : x ＝ w) (q : x ＝ y) (r : y ＝ z)
  (α β : Path-filler p q r)
  where
  faces : (k j i : I) → Partial (∂ k ∨ ∂ j ∨ ~ i) A
  faces k j i (k = i0) = α .snd j i
  faces k j i (k = i1) = β .snd j i
  faces k j i (j = i0) = p i
  faces k j i (j = i1) = r i
  faces k j i (i = i0) = q j

  unique : α ＝ β
  unique k =
    let
      cb : p ⌞ q ⌟ r ⇒ _
      cb j i = hfill (∂ k ∨ ∂ j) i (faces k j)

      sq i = cb i i1
    in sq , λ j i → cb j i

path-comp-unique : ∀ {ℓ} {A : Type ℓ} {x y z : A}
                 → {p : x ＝ y} {q : y ＝ z} (r : x ＝ z)
                 → refl ⌞ p ⌟ q ⇒ r
                 → r ＝ p ∙ q
path-comp-unique {p} {q} r sq i =
  Path-filler.unique refl p q (r , sq) (p ∙ q , path-lfiller p q) i .fst

homotopy-natural : ∀ {u v} {A : Type u} {B : Type v}
                 → {f g : A → B}
                 → (H : (x : A) → f x ＝ g x)
                 → {x y : A} (p : x ＝ y)
                 → H x ∙ ap g p ＝ ap f p ∙ H y
homotopy-natural {f = f} {g = g} H {x} {y} p = path-comp-unique _ λ i j →
  hcomp (~ j ∨ ∂ i) λ where
    k (i = i0) → f x
    k (i = i1) → H (p k) j
    k (j = i0) → f (p (i ∧ k))
    k (k = i0) → H x (i ∧ j)

Σ-PathP
  : ∀ {ℓ ℓ'} {A : I → Type ℓ} {B : ∀ i → A i → Type ℓ'}
  → {x : Σ (B i0)} {y : Σ (B i1)}
  → (p : PathP A (x .fst) (y .fst))
  → PathP (λ i → B i (p i)) (x .snd) (y .snd)
  → PathP (λ i → Σ (B i)) x y
Σ-PathP p q i = p i , q i

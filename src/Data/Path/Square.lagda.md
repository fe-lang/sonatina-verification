```agda
{-# OPTIONS --safe --erased-cubical #-}

module Data.Path.Square where

open import Prim.Type
open import Data.Sigma.Type
open import Data.Path.Base

module _ {ℓ} {A : Type ℓ} where
  -- https://q.uiver.app/#q=WzAsMjEsWzIsMiwieCAiXSxbMiw0LCJ5Il0sWzQsMiwieSJdLFs0LDQsInkiXSxbNCwwLCJ5Il0sWzYsMiwieSJdLFsyLDYsInkiXSxbNCw2LCJ6Il0sWzQsOCwieSJdLFs2LDQsInoiXSxbMCwyLCJ5Il0sWzAsNCwieSJdLFszLDUsImk9aTAiXSxbMyw3LCJrPWkwIl0sWzIsOCwieSJdLFs0LDEwLCJcXGJ1bGxldCJdLFsyLDAsInkiXSxbMSwzLCJqPWkwIl0sWzUsMywiaj1pMSJdLFszLDEsImk9aTEiXSxbMywzLCJrPWkxIl0sWzUsMl0sWzYsMSwiIiwxLHsic3R5bGUiOnsiYm9keSI6eyJuYW1lIjoiZGFzaGVkIn19fV0sWzcsMywicVxcIFxcbmVnIGsiLDFdLFs2LDcsInFcXCBqIiwxXSxbNyw4LCJxXFwgXFxuZWcgaSIsMV0sWzksMywicVxcIFxcbmVnIGsiLDFdLFswLDIsInBcXCBqIiwxXSxbMSwzLCIiLDEseyJzdHlsZSI6eyJib2R5Ijp7Im5hbWUiOiJkYXNoZWQifX19XSxbOSw1LCJxXFwgXFxuZWcgaSIsMV0sWzMsMiwiIiwxLHsic3R5bGUiOnsiYm9keSI6eyJuYW1lIjoiZGFzaGVkIn19fV0sWzEsMCwicFxcIFxcbmVnIGkiLDFdLFsxMSwxMCwiIiwxLHsic3R5bGUiOnsiYm9keSI6eyJuYW1lIjoiZGFzaGVkIn19fV0sWzQsMiwiIiwxLHsic3R5bGUiOnsiYm9keSI6eyJuYW1lIjoiZGFzaGVkIn19fV0sWzEwLDAsInBcXCBcXG5lZyBrIiwxXSxbMTEsMSwiIiwxLHsic3R5bGUiOnsiYm9keSI6eyJuYW1lIjoiZGFzaGVkIn19fV0sWzE0LDgsIiIsMSx7InN0eWxlIjp7ImJvZHkiOnsibmFtZSI6ImRhc2hlZCJ9fX1dLFsxNiwwLCJwXFwgXFxuZWcgayIsMV0sWzE2LDQsIiIsMSx7InN0eWxlIjp7ImJvZHkiOnsibmFtZSI6ImRhc2hlZCJ9fX1dLFs2LDE0LCIiLDEseyJzdHlsZSI6eyJib2R5Ijp7Im5hbWUiOiJkYXNoZWQifX19XSxbMzUsMjIsIiIsMSx7InNob3J0ZW4iOnsic291cmNlIjoyMCwidGFyZ2V0IjoyMH0sInN0eWxlIjp7ImhlYWQiOnsibmFtZSI6Im5vbmUifX19XSxbMzMsMjEsIiIsMSx7InNob3J0ZW4iOnsic291cmNlIjoyMCwidGFyZ2V0IjoyMH0sInN0eWxlIjp7ImhlYWQiOnsibmFtZSI6Im5vbmUifX19XSxbMzQsMzcsIiIsMSx7InNob3J0ZW4iOnsic291cmNlIjoyMCwidGFyZ2V0IjoyMH0sInN0eWxlIjp7ImhlYWQiOnsibmFtZSI6Im5vbmUifX19XSxbMjYsMjMsIiIsMSx7InNob3J0ZW4iOnsic291cmNlIjoyMCwidGFyZ2V0IjoyMH0sInN0eWxlIjp7ImhlYWQiOnsibmFtZSI6Im5vbmUifX19XV0=
  sym-square : {x y z : A} (p : x ＝ y) (q : y ＝ z) → sym p ⌞ q ⌟ sym q ⇒ p
  sym-square {x = x} {y} {z} p q j i =
    let
      α : refl ⌞ refl ⌟ sym p ⇒ sym p
      α i j = p (~ i ∨ ~ j)

      β : sym q ⌞ sym q ⌟ refl ⇒ refl
      β i j = q (~ i ∧ ~ j)

      p=refl : refl ⌞ q ⌟ sym q ⇒ refl
      p=refl j i = q (~ i ∧ j)

      q=refl : sym p ⌞ refl ⌟ refl ⇒ p
      q=refl j i = p (~ i ∨ j)
    in hfill (∂ j ∨ i) i λ where
      k (j = i0) → α i k
      k (j = i1) → β i k
      k (i = i1) → q=refl j k
      k (k = i0) → p=refl j i

  neutral-square : {x y z : A} (p : x ＝ y) (q : y ＝ z) → p ⌞ p ⌟ q ⇒ q
  neutral-square {x = x} {y} {z} p q j i =
    hfill (∂ j ∨ i) i λ where
      k (j = i0) → p (i ∨ k)
      k (j = i1) → q (i ∧ k)
      k (i = i1) → q (j ∧ k)
      k (k = i0) → p (i ∨ j)

  hcomp-fill : {w x y z : A} (p : x ＝ w) (q : x ＝ y) (r : y ＝ z)
            → p ⌞ q ⌟ r ⇒ (p ⌞ q ⌟ r)
  hcomp-fill p q r i j = hfill (∂ i) j (path-faces p q r i)

```
If we have a proof that a path is equal to the hcomp of three paths,
we can fill a square with the four paths.

https://q.uiver.app/#q=WzAsMjEsWzIsMiwidyAiXSxbMiw0LCJ4Il0sWzQsMiwieiJdLFs0LDQsInkiXSxbNCwwLCJ6Il0sWzYsMiwieiJdLFsyLDYsIngiXSxbNCw2LCJ5Il0sWzQsOCwieiJdLFs2LDQsInkiXSxbMCwyLCJ3Il0sWzAsNCwieCJdLFszLDUsImo9aTAiXSxbMyw3LCJrPWkwIl0sWzIsOCwidyJdLFs0LDEwLCJcXGJ1bGxldCJdLFsyLDAsInciXSxbMywzLCJrPWkxIl0sWzMsMSwiaj1pMSJdLFsxLDMsImk9aTAiXSxbNSwzLCJpPWkxIl0sWzUsMiwiIiwxLHsic3R5bGUiOnsiYm9keSI6eyJuYW1lIjoiZGFzaGVkIn19fV0sWzYsMSwiIiwxLHsic3R5bGUiOnsiYm9keSI6eyJuYW1lIjoiZGFzaGVkIn19fV0sWzcsMywiIiwxLHsic3R5bGUiOnsiYm9keSI6eyJuYW1lIjoiZGFzaGVkIn19fV0sWzYsNywicVxcIGkiLDFdLFs3LDgsInJcXCBqIiwxXSxbOSwzLCIiLDEseyJzdHlsZSI6eyJib2R5Ijp7Im5hbWUiOiJkYXNoZWQifX19XSxbMCwyLCJzXFwgaSIsMV0sWzEsMywicVxcIGkiLDFdLFs5LDUsInJcXCBqIiwxLHsic3R5bGUiOnsiYm9keSI6eyJuYW1lIjoiZGFzaGVkIn19fV0sWzMsMiwiclxcIGoiLDFdLFsxLDAsInBcXCBqIiwxXSxbMTEsMTAsInBcXCBqIiwwLHsic3R5bGUiOnsiYm9keSI6eyJuYW1lIjoiZGFzaGVkIn19fV0sWzQsMiwiIiwxLHsic3R5bGUiOnsiYm9keSI6eyJuYW1lIjoiZGFzaGVkIn19fV0sWzEwLDAsIiIsMSx7InN0eWxlIjp7ImJvZHkiOnsibmFtZSI6ImRhc2hlZCJ9fX1dLFsxMSwxLCIiLDEseyJzdHlsZSI6eyJib2R5Ijp7Im5hbWUiOiJkYXNoZWQifX19XSxbNiwxNCwicFxcIGoiLDFdLFsxNCw4LCIocCpxKnIpXFwgaSIsMV0sWzE2LDAsIiIsMSx7InN0eWxlIjp7ImJvZHkiOnsibmFtZSI6ImRhc2hlZCJ9fX1dLFsxNiw0LCIocCpxKnIpXFwgaSIsMSx7InN0eWxlIjp7ImJvZHkiOnsibmFtZSI6ImRhc2hlZCJ9fX1dLFszNSwyMiwiIiwxLHsic2hvcnRlbiI6eyJzb3VyY2UiOjIwLCJ0YXJnZXQiOjIwfSwic3R5bGUiOnsiaGVhZCI6eyJuYW1lIjoibm9uZSJ9fX1dLFszMywyMSwiIiwxLHsic2hvcnRlbiI6eyJzb3VyY2UiOjIwLCJ0YXJnZXQiOjIwfSwic3R5bGUiOnsiaGVhZCI6eyJuYW1lIjoibm9uZSJ9fX1dLFsyNiwyMywiIiwxLHsic2hvcnRlbiI6eyJzb3VyY2UiOjIwLCJ0YXJnZXQiOjIwfSwic3R5bGUiOnsiaGVhZCI6eyJuYW1lIjoibm9uZSJ9fX1dLFszNCwzOCwiIiwxLHsic2hvcnRlbiI6eyJzb3VyY2UiOjIwLCJ0YXJnZXQiOjIwfSwic3R5bGUiOnsiaGVhZCI6eyJuYW1lIjoibm9uZSJ9fX1dXQ==
```
  square-fill : {w x y z : A}
              → (p : x ＝ w) (q : x ＝ y) (r : y ＝ z) (s : w ＝ z)
              → p ⌞ q ⌟ r ＝ s
              → p ⌞ q ⌟ r ⇒ s
  square-fill p q r s H i j =
    hcomp (∂ i ∨ ∂ j) λ where
      k (i = i0) → p j
      k (i = i1) → r j
      k (j = i0) → q i
      k (j = i1) → H k i
      k (k = i0) → hcomp-fill p q r i j

  square-iter : {w x y z : A}
             → (p : x ＝ w) (q : x ＝ y) {r : y ＝ z} {s : w ＝ z}
             → (θ : x ＝ z)
             → ∂ i ↦ θ i ＝ s i , p ＝ refl
             → ∂ i ↦ θ i ＝ r i , q ＝ refl
             → ∂ i ↦ r i ＝ z , r ＝ refl
             → ∂ i ↦ s i ＝ z , s ＝ refl
             → p ⌞ q ⌟ r ⇒ s
  square-iter {z = z} p q θ H K J L i j =
    hcomp (∂ i ∨ ∂ j) λ where
      k (i = i0) → H (~ k) j
      k (i = i1) → J (~ k) j
      k (j = i0) → K (~ k) i
      k (j = i1) → L (~ k) i
      k (k = i0) → z

  syntax square-iter p q H K J L = p , q □⟨ H ⌞ K ⌟ J ⇒ L ⟩_

  sq-crefl-left : {x y z : A} {p : x ＝ y} {q : x ＝ z} {r : y ＝ z}
       → p ⌞ refl ⌟ q ⇒ r → refl ⌞ sym p ⌟ q ⇒ r
  sq-crefl-left {p = p} {q} {r} sq i j =
    hcomp (∂ j ∨ ∂ i) λ where
      k (i = i0) → p (j ∨ k)
      k (i = i1) → q j
      k (j = i0) → p (~ i ∧ k)
      k (j = i1) → r i
      k (k = i0) → sq i j

  sq-crefl-right : {x y z : A} {p : x ＝ y} {q : x ＝ z} {r : y ＝ z}
       → p ⌞ refl ⌟ q ⇒ r → p ⌞ q ⌟ refl ⇒ r
  sq-crefl-right {p = p} {q} {r} sq i j =
    hcomp (∂ j ∨ ∂ i) λ where
      k (i = i0) → p j
      k (i = i1) → q (j ∨ k)
      k (j = i0) → q (i ∧ k)
      k (j = i1) → r i
      k (k = i0) → sq i j

  hcomp-crefl : {x y z : A} (p : x ＝ y) (q : y ＝ z)
             → sym p ⌞ refl ⌟ q ⇒ p ∙ q
  hcomp-crefl {y = y} p q i j =
    hfill (∂ i) j λ where
      k (i = i0) → p (~ j ∧ ~ k) 
      k (i = i1) → q (j ∧ k)
      k (k = i0) → p (i ∨ ~ j)

  hcomp-rrefl : {x y z : A} (p : x ＝ y) (q : y ＝ z)
             → sym p ⌞ q ⌟ refl ⇒ p ∙ q
  hcomp-rrefl p q i j =
    hcomp (∂ i ∨ ~ j) λ where
      k (i = i0) → p (~ j ∧ k)
      k (i = i1) → q k
      k (j = i0) → sym-square p q i (~ k)
      k (k = i0) → p i

  hcomp-lrefl : {x y z : A} (p : x ＝ y) (q : y ＝ z)
             → refl ⌞ sym p ⌟ p ∙ q ⇒ q
  hcomp-lrefl {x = x} {y} {z} p q i j =
    hcomp (∂ j ∨ ~ i) λ where
      k (j = i0) → p (~ i)
      k (j = i1) → q (i ∧ k)
      k (i = i0) → y
      k (k = i0) → p (~ i ∨ j)

Path-filler : ∀ {ℓ} {A : Type ℓ} {w x y z : A}
            → (p : x ＝ w) (q : x ＝ y) (r : y ＝ z) → Type ℓ
Path-filler {w = w} {z = z} p q r =
  Σ s ∶ w ＝ z , p ⌞ q ⌟ r ⇒ s

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

const-sq : ∀ {ℓ} {A : Type ℓ} {a : A} → refl ⌞ refl ⌟ refl ⇒ erefl a
const-sq {a = a} i j = a

sq-hcomp : ∀ {ℓ} {A : Type ℓ} {w x y z : A}
         → {p : x ＝ w} (q : x ＝ y) {r : y ＝ z} (s : w ＝ z)
         → p ⌞ q ⌟ r ⇒ s
         → {a b : A} (q1 : y ＝ a) {r1 : a ＝ b} (s1 : z ＝ b)
         → r ⌞ q1 ⌟ r1 ⇒ s1
         → {c d : A} (q2 : a ＝ c) {r2 : c ＝ d} (s2 : b ＝ d)
         → r1 ⌞ q2 ⌟ r2 ⇒ s2
         → p ⌞ (sym q ⌞ q1 ⌟ q2) ⌟ r2 ⇒ (sym s ⌞ s1 ⌟ s2)
sq-hcomp q {r} s H q1 {r1} s1 K q2 s2 J i j =
  hcomp (∂ i ∨ ∂ j) λ where
   k (i = i0) → H (~ k) j
   k (i = i1) → J k j
   k (j = i0) → hcomp-fill (sym q) q1 q2 i k
   k (j = i1) → hcomp-fill (sym s) s1 s2 i k
   k (k = i0) → γ i j
     where
     γ : r ⌞ q1 ⌟ r1 ⇒ s1
     γ i j = hcomp (∂ j ∨ ∂ i) λ where
       k (i = i0) → r j
       k (i = i1) → K k j
       k (j = i0) → q1 (i ∧ k)
       k (j = i1) → s1 (i ∧ k)
       k (k = i0) → r j

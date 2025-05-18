
```agda
{-# OPTIONS --safe --erased-cubical #-}

module Prim.Data.Path where

open import Prim.Type
open import Prim.Interval.Core
open import Prim.Data.Sigma

```

Open Paths here

```
infixr 2 pathp-syntax

open import Agda.Builtin.Cubical.Path public
  renaming ( _≡_ to infix 2 _＝_ )

Path : ∀ {ℓ} (A : Type ℓ) → A → A → Type ℓ
Path A = PathP (λ _ → A)

pathp-syntax : ∀ {ℓ} (A : I → Type ℓ) → A i0 → A i1 → Type ℓ
pathp-syntax = PathP
syntax pathp-syntax (λ i → b) x y = ∂ i ↦ b , x ＝ y

{-# INLINE pathp-syntax #-}
{-# DISPLAY pathp-syntax A x y = PathP A x y #-}

```

Open basic helpers and fundamental lemmas

```
import Agda.Builtin.Cubical.HCompU
private module H = Agda.Builtin.Cubical.HCompU.Helpers

-- We use standard HoTT terminology for `cong`
open H using ( refl; sym; fiber ) renaming ( cong to ap ) public
{-# INLINE refl #-}
{-# INLINE sym #-}
{-# INLINE fiber #-}

erefl : ∀ {ℓ} {A : Type ℓ} (x : A) → x ＝ x
erefl x = refl
{-# INLINE erefl #-}

```

We'll also define the PathP version of sym:

```

symP : ∀ {ℓ} {A : I → Type ℓ} {x : A i0} {y : A i1}
     → PathP A x y → PathP (λ i → A (~ i)) y x
symP p i = p (~ i)

```

Define Square syntax

```

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

module Square {ℓ} {A : Type ℓ} {a00 a01 a10 a11 : A}
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

-- Introduce (unbiased) path induction. Find its computation rule in Prim.Interval
𝓙 : ∀ {ℓ ℓ'} {A : Type ℓ} (C : (x y : A) → x ＝ y → Type ℓ')
         → (∀ x → C x x refl) → ∀ {u v} (w : u ＝ v) → C u v w
𝓙 C c {u} w = transp (λ i → C u (w i) (λ j → w (i ∧ j))) i0 (c u)

-- Finally we introduce transport along with its 2-dimensional variant
subst : ∀ {ℓ ℓ'} {A : Type ℓ} (P : A → Type ℓ')
  → {x y : A} → x ＝ y → P x → P y
subst P {x} q = transp (λ i → P (q i)) i0

subst2 : ∀ {u v w} {A : Type u} {B : A → Type v}
    → (P : (x : A) → B x → Type w)
    → {a a' : A} {b : B a} {b' : B a'}
    → (p : a ＝ a') → (∂ i ↦ B (p i) , b ＝ b')
    → P a b → P a' b'
subst2 P p q = transp (λ i → P (p i) (q i)) i0

⟨_⟩₁ : ∀ {ℓ} {A : Type ℓ} → A → Type ℓ
⟨_⟩₁ {A = A} x = Σ (x ＝_)

singl-contr : ∀ {ℓ} {A : Type ℓ} {x : A} (s : ⟨ x ⟩₁) → x , refl ＝ s
singl-contr (y , p) = λ i → p i , λ j → p (i ∧ j)

-- Based path induction
J : ∀ {u v} {A : Type u} {x : A} (P : (y : A) → x ＝ y → Type v)
  → P x refl → (y : A) (q : x ＝ y) → P y q
J {v} {A} {x} P c y q =
  let
    Q : ⟨ x ⟩₁ → Type v
    Q s = P (s .fst) (s .snd)

    sing : x , refl ＝ y , q
    sing = singl-contr (y , q)
  in
    subst2 (λ z r → Q (z , r)) q  (ap snd sing) c

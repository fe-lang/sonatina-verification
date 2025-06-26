
```agda
{-# OPTIONS --safe --erased-cubical #-}

module Data.Path.Type where

open import Prim.Type
open import Prim.Interval
open import Prim.Kan

open import Data.Sigma.Type

open import Meta.Cut public
open import Meta.Bracket public

```

Open Paths here

```
infixr 2 pathp-syntax
infixr 40 _∙∙_∙∙_

open import Agda.Builtin.Cubical.Path public
  renaming ( _≡_ to infix 2 _＝_ )

Path : ∀ {ℓ} (A : Type ℓ) → A → A → Type ℓ
Path A = PathP (λ _ → A)

path-syntax : ∀ {ℓ} (A : Type ℓ) → A → A → Type ℓ
path-syntax A = PathP (λ _ → A)
syntax path-syntax A x y = x ＝ y ∶ A

pathp-syntax : ∀ {ℓ} (A : I → Type ℓ) → A i0 → A i1 → Type ℓ
pathp-syntax = PathP
syntax pathp-syntax (λ i → b) x y = ∂ i ↦ b , x ＝ y

{-# INLINE pathp-syntax #-}
{-# DISPLAY pathp-syntax A x y = PathP A x y #-}

refl : ∀ {u} {A : Type u} {x : A} → x ＝ x
refl {x} i = x
{-# INLINE refl #-}

erefl : ∀ {ℓ} {A : Type ℓ} (x : A) → x ＝ x
erefl x = refl
{-# INLINE erefl #-}

sym : ∀ {ℓ} {A : I → Type ℓ} {x : A i0} {y : A i1}
     → ∂ i ↦ A i , x ＝ y → ∂ i ↦ A (~ i) , y ＝ x
sym p i = p (~ i)
{-# INLINE sym #-}

instance
  Canonical-Path : ∀ {ℓ} {A : Type ℓ} → Canonical-map λ (x : A) → x ＝ x
  Canonical-Path .Canonical-map.map = erefl

ap : ∀ {u v} {A : Type u} {B : A → Type v}
   → (f : ∀ a → B a)
   → {x y : A}
   → (p : x ＝ y)
   → ∂ i ↦ B (p i) , f x ＝ f y
ap f p i = f (p i)
{-# INLINE ap #-}

casei_of_ : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} (x : A) → ((y : A) → x ＝ y → B) → B
casei x of f = f x (λ i → x)
{-# INLINE casei_of_ #-}

casei_return_of_ : ∀ {ℓ ℓ'} {A : Type ℓ} (x : A) (P : A → Type ℓ') → ((y : A) → x ＝ y → P y) → P x
casei x return P of f = f x (λ i → x)
{-# INLINE casei_return_of_ #-}

fiber : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} → (A → B) → B → Type (ℓ ⊔ ℓ')
fiber {A} f y = Σ x ∶ A , (f x ＝ y)

funext : ∀ {ℓ ℓ'} {A : Type ℓ} {B : A → Type ℓ'} {f g : (x : A) → B x}
       → ((x : A) → f x ＝ g x) → f ＝ g
funext p i x = p x i

funexti : ∀ {ℓ} {A : I → Type ℓ} {f g : (i : I) → A i}
       → ((i : I) → f i ＝ g i) → f ＝ g
funexti p i j = p j i

happly : ∀ {a b} {A : Type a} {B : A → Type b} {f g : (x : A) → B x}
       → f ＝ g → (x : A) → f x ＝ g x
happly p x i = p i x

transport : ∀ {u} {A B : Type u} → A ＝ B → A → B
transport p = coe (λ i → p i) i1

PathD : ∀ {u v} {A : Type u} (B : A → Type v) {x y : A}
      → (p : x ＝ y) → B (p i0) → B (p i1) → Type v
PathD B p a b = PathP (λ i → B (p i)) a b

Path-over : ∀ {u} (A : I → Type u) → A i0 → A i1 → Type u
Path-over A x y = coe.0→1 A x ＝ y

module Path-over {u} {A : I → Type u} {x : A i0} {y : A i1} where
  to-pathp : Path-over A x y → PathP A x y
  to-pathp p i = hcomp (∂ i) λ where
    j (i = i0) → x
    j (i = i1) → p j
    j (j = i0) → coe A i x

  from-pathp : PathP A x y → Path-over A x y
  from-pathp p i = transp (λ j → A (i ∨ j)) i (p i)

Path-over＝PathP : ∀ {ℓ} (P : I → Type ℓ) (p : P i0) (q : P i1)
           → Path-over P p q ＝ PathP P p q
Path-over＝PathP P p q i = PathP (λ j → P (~ i ∨ j)) (coe.sys (λ j → P j) p i1 (~ i)) q

path-sys : ∀ {ℓ} {A : I → Type ℓ}
               → {x w : A i0} {y z : A i1}
               → x ＝ w
               → PathP A x y
               → y ＝ z
               → (i j : I) → Partial (∂ i ∨ ~ j) (A i)
path-sys p q r i j (i = i0) = p j
path-sys p q r i j (i = i1) = r j
path-sys p q r i j (j = i0) = q i

lid : ∀ {ℓ} {A : Type ℓ} {w x y z : A} → x ＝ w → x ＝ y → y ＝ z → w ＝ z
lid p q r i = hcomp (∂ i) (path-sys p q r i)

```

-- Agda-cubical's Cubical.Foundations.Prelude module states that
-- double-composition is the most "natural" notion of composition
-- in Cubical Type Theory, and indeed it is true. In the following
-- diagram (borrowed from the aforementioned module) we are shown
-- that in CTT when we have the data of three commuting paths, this
-- is sufficient to form the connecting path between w and z. Hcomp
-- can compute on any type indexed by the interval, but when we use
-- it for paths this is its natural presentation:


-- >        w ∙ ∙ ∙ > z
-- >        ^         ^
-- >      p |         | r        ^
-- >        |         |        j |
-- >        x — — — > y          ∙ — >
-- >             q                 i
-- >
-- >  `p ⌞ q ⌟ r` gives the line at the top,

```
-- The traditional double-composition operator
_∙∙_∙∙_ : ∀ {ℓ} {A : Type ℓ} {w x y z : A} → w ＝ x → x ＝ y → y ＝ z → w ＝ z
p ∙∙ q ∙∙ r = lid (sym p) q r

instance
  Cut-pathcomp : ∀ {u} {A : Type u} → Hom-Cut (_＝_ {A = A})
  Cut-pathcomp .Cut.seq = refl ∙∙_∙∙_

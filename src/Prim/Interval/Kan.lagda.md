```agda

{-# OPTIONS --safe --erased-cubical #-}

module Prim.Interval.Kan where

open import Prim.Type using (Level; Type)
open import Prim.Pi using (flip)
open import Prim.Data.Path using (_＝_; refl; sym; Square; PathP)
open import Prim.Interval.Core

open import Agda.Primitive.Cubical using (primComp; primHComp) public
open import Agda.Builtin.Cubical.HCompU public
  using (prim^glueU; prim^unglueU; transpProof)

one-faces : ∀ {ℓ} {A : Type ℓ} (φ : I)
            → (u : (i : I) → Partial (φ ∨ ~ i) A)
            → (i : I) → Partial (φ ∨ ~ i) A
one-faces φ u i (i = i0) = u i0 1=1
one-faces φ u i (φ = i1) = u i  1=1

partial-pushout
  : ∀ {ℓ} (i j : I) {A : Partial (i ∨ j) (Type ℓ)}
    {ai : PartialP {a = ℓ} (i ∧ j) (λ { (j ∧ i = i1) → A 1=1 }) }
  → (.(z : IsOne i) → A (is1-left  i j z) [ (i ∧ j) ↦ (λ { (i ∧ j = i1) → ai 1=1 }) ])
  → (.(z : IsOne j) → A (is1-right i j z) [ (i ∧ j) ↦ (λ { (i ∧ j = i1) → ai 1=1 }) ])
  → PartialP (i ∨ j) A
partial-pushout i j u v = primPOr i j (λ z → outS (u z)) (λ z → outS (v z))

hcomp-faces : ∀ {ℓ} {A : Type ℓ} (φ : I)
            → (u : (i : I) → Partial (φ ∨ ~ i) A)
            → (i : I) → Partial φ A
hcomp-faces φ u j o = u j (is1-left φ (~ j) o)

hcomp-base : ∀ {ℓ} {A : Type ℓ} (φ : I)
             → (u : (i : I) → Partial (φ ∨ ~ i) A)
             → A
hcomp-base φ u = u i0 1=1

hcomp : ∀ {ℓ} {A : Type ℓ} (φ : I)
      → (u : (i : I) → Partial (φ ∨ ~ i) A) → A
hcomp φ u = primHComp (λ j .o → u j (is1-left φ (~ j) o)) (u i0 1=1)

hcomp-unique : ∀ {ℓ} {A : Type ℓ} (φ : I)
               (u : ∀ i → Partial (φ ∨ ~ i) A)
             → (h₂ : ∀ i → A [ _ ↦ one-faces φ u i ])
             → hcomp φ u ＝ outS (h₂ i1)
hcomp-unique φ u h₂ i =
  hcomp (φ ∨ i) λ where
    k (k = i0) → u i0 1=1
    k (i = i1) → outS (h₂ k)
    k (φ = i1) → u k 1=1

hfill : ∀ {ℓ} {A : Type ℓ} (φ : I) → I
      → ((i : I) → Partial (φ ∨ ~ i) A)
      → A
hfill φ i u =
  hcomp (φ ∨ ~ i) λ where
    j (i = i0) → u i0      1=1
    j (j = i0) → u i0      1=1
    j (φ = i1) → u (i ∧ j) 1=1

comp : {ℓ^ : I → Level} (A : (i : I) → Type (ℓ^ i)) (φ : I)
     → (u : (i : I) → Partial (φ ∨ ~ i) (A i))
     → A i1
comp A φ u = primComp A (λ j .o → u j (is1-left φ (~ j) o)) (u i0 1=1)

fill : {ℓ^ : I → Level} (A : ∀ i → Type (ℓ^ i)) (φ : I) (i : I)
     → (u : ∀ i → Partial (φ ∨ ~ i) (A i))
     → A i
fill A φ i u = comp (λ j → A (i ∧ j)) (φ ∨ ~ i) λ where
  j (i = i0) → u i0 1=1
  j (j = i0) → u i0 1=1
  j (φ = i1) → u (i ∧ j) 1=1

```

Agda-cubical's Cubical.Foundations.Prelude module states that
double-composition is the most "natural" notion of composition
in Cubical Type Theory, and indeed it is true. In the following
diagram (borrowed from the aforementioned module) we are shown
that in CTT when we have the data of three commuting paths, this
is sufficient to form the connecting path between w and z. Hcomp
can compute on any type indexed by the interval, but when we use
it for paths this is its natural presentation:


>        w ∙ ∙ ∙ > z
>        ^         ^
>      p |         | r        ^
>        |         |        j |
>        x — — — > y          ∙ — >
>             q                 i
>
>  `p ⌞ q ⌟ r` gives the line at the top,

(Note: Unlike the usual definition we choose to make
double composition follow the diagram exactly, rather than
inverting `p : w ＝ x`, our version has `p : x ＝ w`.)

```

path-faces : ∀ {ℓ} {A : I → Type ℓ}
               → {x w : A i0} {y z : A i1}
               → x ＝ w
               → PathP A x y
               → y ＝ z
               → (i j : I) → Partial (∂ i ∨ ~ j) (A i)
path-faces p q r i j (i = i0) = p j
path-faces p q r i j (i = i1) = r j
path-faces p q r i j (j = i0) = q i

_⌞_⌟_ : ∀ {ℓ} {A : Type ℓ} {w x y z : A} → x ＝ w → x ＝ y → y ＝ z → w ＝ z
(p ⌞ q ⌟ r) i = hcomp (∂ i) (path-faces p q r i)

{-# NOINLINE _⌞_⌟_ #-}

path-filler : ∀ {ℓ} {A : Type ℓ}  {w x y z : A}
            → (p : x ＝ w) (q : x ＝ y) (r : y ＝ z)
            → p ⌞ q ⌟ r ⇒ (p ⌞ q ⌟ r)
path-filler p q r i j = hfill (∂ i) j (path-faces p q r i)

-- The traditional double-composition operator
_∙∙_∙∙_ : ∀ {ℓ} {A : Type ℓ} {w x y z : A} → w ＝ x → x ＝ y → y ＝ z → w ＝ z
p ∙∙ q ∙∙ r = sym p ⌞ q ⌟ r

```

From which we choose a canonical single-composition definition

```

path-comp : ∀ {ℓ} {A : Type ℓ} {x y z : A} → x ＝ y → y ＝ z → x ＝ z
path-comp {x = x} {y} p q = refl ⌞ p ⌟ q

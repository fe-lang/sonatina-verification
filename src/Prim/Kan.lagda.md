```agda

{-# OPTIONS --safe --erased-cubical #-}

module Prim.Kan where

open import Prim.Type using (Level; Type)
open import Prim.Interval

private module X where
  open import Agda.Primitive.Cubical public using (primTransp; primHComp; primComp)
open X public renaming (primTransp to transp) using (primHComp) public

hcomp : ∀ {ℓ} {A : Type ℓ} (φ : I)
      → (u : (i : I) → Partial (φ ∨ ~ i) A) → A
hcomp {A = A} φ u = X.primHComp sys (u i0 1=1)
  module hcomp where
    sys : ∀ j → Partial φ A
    sys j (φ = i1) = u j 1=1

comp : {ℓ : I → Level} (A : (i : I) → Type (ℓ i)) (φ : I)
     → (u : (i : I) → Partial (φ ∨ ~ i) (A i))
     → A i1
comp A φ u = X.primHComp sys (transp A i0 (u i0 1=1))
  module comp where
    sys : ∀ j → Partial φ (A i1)
    sys i (φ = i1) = transp (λ j → A (i ∨ j)) i (u i 1=1)

fill : {ℓ : I → Level} (A : ∀ i → Type (ℓ i)) (φ : I) (i : I)
     → (u : ∀ i → Partial (φ ∨ ~ i) (A i))
     → A i
fill A φ i u = comp (λ j → A (i ∧ j)) (φ ∨ ~ i) λ where
  j (i = i0) → u i0 1=1
  j (j = i0) → u i0 1=1
  j (φ = i1) → u (i ∧ j) 1=1

hfill : ∀ {ℓ} {A : Type ℓ} (φ : I) → I
      → ((i : I) → Partial (φ ∨ ~ i) A)
      → A
hfill φ i u =
  hcomp (φ ∨ ~ i) λ where
    j (i = i0) → u i0      1=1
    j (j = i0) → u i0      1=1
    j (φ = i1) → u (i ∧ j) 1=1

-- {-# DISPLAY X.primHComp {ℓ} {A} {φ} (hcomp.sys _ u) _ = hcomp {ℓ} {A} φ u #-}
-- {-# DISPLAY X.primHComp {_} {_} {φ} (comp.sys A _ u) _ = comp A φ u #-}

module coe where
  open import Agda.Builtin.Cubical.Path using (PathP)
  0→i : {ℓ : I → Level} (A : ∀ i → Type (ℓ i)) (i : I) → A i0 → A i
  0→i A i a = transp (λ j → A (i ∧ j)) (~ i) a

  i→0 : {ℓ : I → Level} (A : ∀ i → Type (ℓ i)) (i : I) → A i → A i0
  i→0 A i a = transp (λ j → A (i ∧ ~ j)) (~ i) a

  i→1 : {ℓ : I → Level} (A : ∀ i → Type (ℓ i)) (i : I) → A i → A i1
  i→1 A i = transp (λ j → A (i ∨ j)) i

  1→i : {ℓ : I → Level} (A : ∀ i → Type (ℓ i)) (i : I) → A i1 → A i
  1→i A i = transp (λ j → A (i ∨ ~ j)) i

  0→1 : {ℓ : I → Level} (A : ∀ i → Type (ℓ i)) → A i0 → A i1
  0→1 A a = transp (λ j → A j) i0 a

  sys : ∀ {ℓ} (A : I → Type ℓ) (x : A i0) (i : I)
         → PathP (λ j → A (i ∧ j)) x (0→i A i x)
  sys A x i j = 0→i A (i ∧ j) x

open coe public renaming (0→i to coe) using ()

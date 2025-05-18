```agda
{-# OPTIONS --safe --erased-cubical #-}

module Prim.Fiber where

open import Prim.Type
open import Prim.Interval.Core
open import Prim.Interval.Kan
  using (hcomp; hfill; path-filler)
  renaming (path-comp to _∙_)
open import Prim.Interval.Fill using (neutral-square; module tri)

open import Prim.Data.Path
open import Prim.Data.Contr
open import Prim.Data.Qinv
open import Prim.Data.Sigma

record is-fequiv {u v} {A : Type u} {B : Type v} (f : A → B) : Type (u ⊔ v) where
  no-eta-equality
  field
    is-feqv : (y : B) → is-contr (fiber f y)

open is-fequiv public

strict-fibers : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'}
              → (f : A → B) (g : B → A) (y : B)
              → Σ (λ (z : (fiber f (f (g y)))) →
                  ((x , p) : fiber f y) → z ＝ g (f x) , ap (λ z → f (g z)) p)
strict-fibers f g b .fst = (g b , refl)
strict-fibers f g b .snd (a , p) i =
  (g (p (~ i)) , λ j → f (g (p (~ i ∨ j))))

module qinv→contr-fibers {u v} {A : Type u} {B : Type v}
  (q : Qinv A B)
  where
  private
    f = q .fst
    g = q .snd .qinv-inv
    η = q .snd .qinv-sec
    ε = q .snd .qinv-retr

  module _ {y : B} ((x , p) : fiber f y) where
    faces0 : (i j : I) → Partial (∂ i ∨ ~ j) A
    faces0 i = λ where
      k (i = i0) → g y
      k (i = i1) → η (g y) k
      k (k = i0) → g (ε y (~ i))

    faces1 : (i j : I) → Partial (∂ i ∨ ~ j) A
    faces1 i = λ where
      k (i = i0) → g y
      k (i = i1) → η x k
      k (k = i0) → g (p (~ i))

    private
      π₀ : g y ＝ g y
      π₀ i = hcomp (∂ i) (faces0 i)

      θ₀ : refl ⌞ ap g (sym (ε y)) ⌟ η (g y) ⇒ π₀
      θ₀ i j = hfill (∂ i) j (faces0 i)

      π₁ : g y ＝ x
      π₁ i = hcomp (∂ i) (faces1 i)

      θ₁ : refl ⌞ ap g (sym p) ⌟ η x  ⇒ π₁
      θ₁ i j = hfill (∂ i) j (faces1 i)

      fiber-faces : (i j : I) → Partial (∂ i ∨ ~ j) A
      fiber-faces i = λ where
        j (i = i0) → π₀ j
        j (i = i1) → π₁ j
        j (j = i0) → g y

      path : g y ＝ x
      path i = hcomp (∂ i) (fiber-faces i)

      fiber-filler : π₀ ⌞ refl ⌟ π₁ ⇒ path
      fiber-filler i j = hfill (∂ i) j (fiber-faces i)

      ι : ap g (ε y) ⌞ ap (λ z → g (f z)) path ⌟ ap g p ⇒ refl
      ι i j = hcomp (∂ i ∨ ∂ j) λ where
        k (i = i0) → θ₀ (~ j) (~ k)
        k (i = i1) → θ₁ (~ j) (~ k)
        k (j = i0) → η (path i) (~ k)
        k (j = i1) → g y
        k (k = i0) → fiber-filler i (~ j)

      filler : ε y ⌞ ap f path ⌟ p ⇒ refl
      filler i j = hcomp (∂ i ∨ ∂ j) λ where
        k (i = i0) → ε (ε y j) k
        k (i = i1) → ε (p j) k
        k (j = i0) → ε (f (path i)) k
        k (j = i1) → ε y k
        k (k = i0) → f (ι i j)

    unit : g (f x) ＝ x
    unit i = hcomp (∂ i) λ where
      j (i = i0) → g (f x)
      j (i = i1) → path j
      j (j = i0) → g (p i)

    counit : f (g y) ＝ y
    counit = ε y

    private
      φ : Square refl p (sym (ε y)) (ap f (sym path))
      φ = tri.by-comp (sym (ε y)) (ap f path) (sym p) (Square.rrotate filler)

    adj : ap f unit ＝ ε (f x)
    adj i j = hcomp (∂ i ∨ ∂ j) λ where
      k (i = i0) → f (path-filler refl (ap g p) path j k)
      k (i = i1) → ε (p (~ k)) j
      k (j = i0) → f (g (p (i ∧ ~ k)))
      k (j = i1) → φ (~ k) (~ i)
      k (k = i0) → neutral-square (ap (λ z → (f (g z))) p) (ε y) i j

    fiber-path : Path (fiber f y) (g y , ε y) (x , p)
    fiber-path i .fst = path i
    fiber-path i .snd = filler i

  contr : (y : B) → is-contr (fiber f y)
  contr y .ctr = g y , ε y
  contr y .paths = fiber-path

  fequiv : is-fequiv f
  fequiv .is-fequiv.is-feqv = contr
  {-# INLINE fequiv #-}

open qinv→contr-fibers public
  renaming ( contr to qinv→contr-fibers
           ; fequiv to qinv→fequiv )
  using ()

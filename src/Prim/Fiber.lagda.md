```agda
{-# OPTIONS --safe --erased-cubical #-}

module Prim.Fiber where

open import Prim.Type
open import Prim.Data.Path
open import Prim.Cubical
open import Prim.Kan using (hcomp; hfill)
open import Prim.Fill
  using (hcomp-fill; neutral-square; sq-refl-top)
open import Prim.Kan
  renaming (path-comp to _∙_)
  using ()

open import Agda.Builtin.Sigma

strict-fibers : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} {f : A → B}
              → (g : B → A) (y : B)
              → Σ (fiber f (f (g y)))
                  (λ (z : fiber f (f (g y)))
                        → ((x , p) : fiber f y)
                        → z ＝ g (f x) , ap (λ z → f (g z)) p)
strict-fibers {f = f} g b .fst = (g b , refl)
strict-fibers {f = f} g b .snd (a , p) i =
  (g (p (~ i)) , λ j → f (g (p (~ i ∨ j))))

module contr-fibers {u v} {A : Type u} {B : Type v}
  (f : A → B) (g : B → A)
  (η : (x : A) → g (f x) ＝ x)
  (ε : (y : B) → f (g y) ＝ y)
  {y : B} ((x , p) : fiber f y)
  where
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

  path-faces : (i j : I) → Partial (∂ i ∨ ~ j) A
  path-faces i = λ where
    j (i = i0) → π₀ j
    j (i = i1) → π₁ j
    j (j = i0) → g y

  path : g y ＝ x
  path i = hcomp (∂ i) (path-faces i)

  path-filler : π₀ ⌞ refl ⌟ π₁ ⇒ path
  path-filler i j = hfill (∂ i) j (path-faces i)

  private
    ι : ap g (ε y) ⌞ ap (λ z → g (f z)) path ⌟ ap g p ⇒ refl
    ι i j = hcomp (∂ i ∨ ∂ j) λ where
      k (i = i0) → θ₀ (~ j) (~ k)
      k (i = i1) → θ₁ (~ j) (~ k)
      k (j = i0) → η (path i) (~ k)
      k (j = i1) → g y
      k (k = i0) → path-filler i (~ j)

  filler : ε y ⌞ ap f path ⌟ p ⇒ refl
  filler i j = hcomp (∂ i ∨ ∂ j) λ where
    k (i = i0) → ε (ε y j) k
    k (i = i1) → ε (p j) k
    k (j = i0) → ε (f (path i)) k
    k (j = i1) → ε y k
    k (k = i0) → f (ι i j)

  unit : g (f x) ＝ x
  unit = ap g p ∙ path

  counit : f (g y) ＝ y
  counit = ε y

  zig : ap f unit ＝ ε (f x)
  zig i j = hcomp (∂ i ∨ ∂ j) λ where
    k (i = i0) → f (hcomp-fill refl (ap g p) path j k)
    k (i = i1) → ε (p (~ k)) j
    k (j = i0) → f (g (p (i ∧ ~ k)))
    k (j = i1) → sq-refl-top (ε y) (ap f path) p filler i k
    k (k = i0) → neutral-square (ap (λ z → (f (g z))) p) (ε y) i j

  contr-fibers : Path (fiber f y) (g y , ε y) (x , p)
  contr-fibers i .fst = path i
  contr-fibers i .snd = filler i

open contr-fibers using ( contr-fibers ) public

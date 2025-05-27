```agda
{-# OPTIONS --safe --erased-cubical #-}

module Data.Path.Base where

open import Prim.Type
open import Prim.Interval
open import Prim.Kan
open import Prim.Sub
open import Meta.Cut

open import Data.Sigma.Type
open import Data.Path.Type public

-- Introduce (unbiased) path induction. Find its computation rule in Prim
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

module _ {ℓ ℓ'} where
  aps : {A : Type ℓ} {B : Type ℓ'} {x y : A} (f : A → B) → x ＝ y → f x ＝ f y
  aps f p i = f (p i)
  {-# INLINE aps #-}

  apd : {A : I → Type ℓ} {B : (i : I) → A i → Type ℓ'}
      → (f : (i : I) → (a : A i) → B i a) {x : A i0} {y : A i1}
      → (p : PathP A x y)
      → ∂ i ↦ B i (p i) , f i0 x ＝ f i1 y
  apd f p i = f i (p i)
  {-# INLINE apd #-}

module _ {u v w} {A : Type u} where
  ap2 : {B : A → Type v} {C : (s : A) → B s → Type w}
      → (f : (s : A) (t : B s) → C s t) {x y : A} {a : B x} {b : B y}
      → (p : x ＝ y) (q : ∂ i ↦ B (p i) , a ＝ b)
      → ∂ i ↦ C (p i) (q i) , f x a ＝ f y b
  ap2 f p q i = f (p i) (q i)
  {-# INLINE ap2 #-}

  ap2s : {B : Type v} {C : A → B → Type w}
       → (f : (s : A) (t : B) → C s t) {x y : A} {a b : B}
       → (p : x ＝ y) (q : a ＝ b)
       → ∂ i ↦ C (p i) (q i) , f x a ＝ f y b
  ap2s f p q i = f (p i) (q i)
  {-# INLINE ap2s #-}

hcomp-unique : ∀ {ℓ} {A : Type ℓ} (φ : I)
             → (u : ∀ i → Partial (φ ∨ ~ i) A)
             → (h2 : ∀ i → A [ _ ↦ (λ where (φ = i1) → u i 1=1
                                            (i = i0) → u i0 1=1) ])
             → hcomp φ u ＝ outS (h2 i1)
hcomp-unique φ u h2 i =
  hcomp (φ ∨ i) λ where
    k (k = i0) → u i0 1=1
    k (i = i1) → outS (h2 k)
    k (φ = i1) → u k 1=1

```agda

{-# OPTIONS --safe --erased-cubical #-}

module Prim.Interval.Transport where

open import Prim.Type renaming (funcomp to infixr 40 _∘_)
open import Prim.Interval.Kan using (hcomp; comp; hfill; fill; path-filler)
  renaming (path-comp to infixr 40 _∙_)
open import Prim.Interval.Fill using ( module tri; neutral-square )

open import Prim.Data.Contr
open import Prim.Data.Sigma
open import Prim.Data.Path
open import Prim.Data.Qinv

open import Prim.Interval.Core public

```

Notions of dependent path composition

```

module _ {ℓ} {A : I → Type ℓ} {x : A i0} {y : A i1}
  {B_i1 : Type ℓ} {B : A i1 ＝ B_i1} {z : B i1}
  (p : PathP A x y)
  (q : PathP (λ i → B i) y z)
  (let C : I → I → Type ℓ
       C i j = path-filler refl (λ k → A k) B i j)
  where
  pathp-faces : (i j : I) → Partial (∂ i ∨ ~ j) (C i j)
  pathp-faces i j (i = i0) = x
  pathp-faces i j (i = i1) = q j
  pathp-faces i j (j = i0) = p i

  pathp-comp : ∂ j ↦ ((λ i → A i) ∙ B) j , x ＝ z
  pathp-comp i = comp (C i) (∂ i) (pathp-faces i)

  pathp-filler : ∂ i ↦ ∂ j ↦ C j i , x ＝ q i , p ＝ pathp-comp
  pathp-filler j i = fill (C i) (∂ i) j (pathp-faces i)

module _ {ℓ ℓ'} {A : Type ℓ} {B : A → Type ℓ'}
  {x y z : A} {x' : B x} {y' : B y} {z' : B z}
  {p : x ＝ y} {q : y ＝ z}
  (p' : ∂ i ↦ B (p i) , x' ＝ y')
  (q' : ∂ i ↦ B (q i) , y' ＝ z')
  (let C : (i j : I) → Type ℓ'
       C i j = B (path-filler refl p q i j))
  where
  pathp-dep-faces : (i j : I) → Partial (∂ i ∨  ~ j) (C i j)
  pathp-dep-faces i j (i = i0) = x'
  pathp-dep-faces i j (i = i1) = q' j
  pathp-dep-faces i j (j = i0) = p' i

  pathp-depcomp : ∂ i ↦ B ((p ∙ q) i) , x' ＝ z'
  pathp-depcomp i = comp (C i) (∂ i) (pathp-dep-faces i)

  pathp-dep-fill : ∂ i ↦ ∂ j ↦ C j i , x' ＝ q' i , p' ＝ pathp-depcomp
  pathp-dep-fill j i = fill (C i) (∂ i) j (pathp-dep-faces i)


coe : {ℓ : I → Level} (A : ∀ i → Type (ℓ i)) → (i : I) → A i0 → A i
coe A i a = transp (λ j → A (i ∧ j)) (~ i) a
{-# INLINE coe #-}

module coe where
  op : {ℓ : I → Level} (A : ∀ i → Type (ℓ i)) (i : I) → A i → A i0
  op A i a = transp (λ j → A (i ∧ ~ j)) (~ i) a
  {-# INLINE op #-}

  i→1 : {ℓ : I → Level} (A : ∀ i → Type (ℓ i)) (i : I) → A i → A i1
  i→1 A i = transp (λ j → A (i ∨ j)) i

  1→i : {ℓ : I → Level} (A : ∀ i → Type (ℓ i)) (i : I) → A i1 → A i
  1→i A i = transp (λ j → A (i ∨ ~ j)) i

  filler : ∀ {ℓ} (A : I → Type ℓ) (x : A i0) (i : I)
         → PathP (λ j → A (i ∧ j)) x (coe A i x)
  filler A x i j = coe A (i ∧ j) x

transport : ∀ {ℓ} {A B : Type ℓ} (P : A ＝ B) → P i0 → P i1
transport P = transp (λ i → P i) i0
{-# INLINE transport #-}

transport-refl : ∀ {ℓ} {A : Type ℓ} (x : A) → transport (λ _ → A) x ＝ x
transport-refl {A = A} x i = coe.filler (λ _ → A) x (~ i) i1

𝓙-refl : ∀ {ℓ ℓ'} {A : Type ℓ} (C : (x y : A) → x ＝ y → Type ℓ')
              → (c : (a : A) → C a a (λ i → a)) (x : A)
              → 𝓙 C c (λ i → x) ＝ c x
𝓙-refl C c x = transport-refl (c x)

module transport where
  filler : ∀ {ℓ} {A B : Type ℓ} (p : A ＝ B) (x : A)
         → ∂ i ↦ p i , x ＝ transport p x
  filler P x i = coe.filler (λ i → P i) x i i

  op : ∀ {ℓ} {A B : Type ℓ} (P : A ＝ B) → P i1 → P i0
  op P = transport (sym P)

  op-refl : ∀ {ℓ} {A : Type ℓ} (x : A) → transport (λ _ → A) x ＝ x
  op-refl {A = A} x i = filler (λ _ → A) x (~ i)

  -- TODO: Write passage crediting 1lab and Cohen for proof
  idfun-filler : ∀ {ℓ} (A : I → Type ℓ) → ∂ i ↦ (A i0 → A i) , id ＝ coe A i1
  idfun-filler A i = coe (λ i → A i) i

  op-idfun-filler : ∀ {ℓ} (A : I → Type ℓ) → PathP (λ i → A i1 → A i) (op (λ i → A i)) id
  op-idfun-filler A i = coe (λ i → A (~ i)) (~ i)

  has-fiber : ∀ {ℓ} (A : I → Type ℓ) (y : A i1)
            → fiber (coe A i1) y
  has-fiber A y .fst = op (λ i → A i) y
  has-fiber A y .snd i = comp (λ i → A i) (∂ i) λ where
    j (i = i0) → idfun-filler A j (op (λ i → A i) y)
    j (i = i1) → op-idfun-filler A j y
    j (j = i0) → op (λ i → A i) y

  private
    module _ {ℓ} (A : I → Type ℓ) (y : A i1)
      ((x1 , p1) : fiber (coe A i1) y)
      where
      x0 : A i0
      x0 = has-fiber A y .fst

      p0 : coe A i1 x0 ＝ y
      p0 = has-fiber A y .snd

      P : A i0 ＝ A i1
      P = λ i → A i

      f = coe A i1
      g = op (λ i → A i)

      u = idfun-filler (λ i → A i)
      v = op-idfun-filler (λ i → A i)

      faces : (x : A i0) (β : f x ＝ y) (i j : I)
            → PartialP (∂ i ∨ (~ j)) (λ _ → P (~ j))
      faces x β i j (i = i0) = v (~ j) y
      faces x β i j (i = i1) = u (~ j) x
      faces x β i j (j = i0) = β (~ i)

      w0 : g y ＝ x0
      w0 i = comp (λ j → P (~ j)) (∂ i) (faces x0 p0 i)

      w1 : g y ＝ x1
      w1 i = comp (λ j → P (~ j)) (∂ i) (faces x1 p1 i)

      sq0 : SquareP (λ _ j → P (~ j)) (λ i → v (~ i) y) (sym p0) (λ i → u (~ i) x0) w0
      sq0 i j = fill (λ k → P (~ k)) (∂ i) j (faces x0 p0 i)

      sq1 : SquareP (λ _ z → A (~ z)) (λ i → v (~ i) y) (sym p1) (λ i → u (~ i) x1) w1
      sq1 i j = fill (λ k → A (~ k)) (∂ i) j (faces x1 p1 i)

      w : x0 ＝ x1
      w i = hcomp (∂ i) λ where
        j (i = i0) → w0 j
        j (i = i1) → w1 j
        j (j = i0) → g y

      sq : Square w0 refl w1 w
      sq i j = hfill (∂ i) j λ where
        k (i = i0) → w0 k
        k (i = i1) → w1 k
        k (k = i0) → g y

      cb : Square (sym p0) refl (sym p1) (ap f w)
      cb i j = comp A (∂ i ∨ ∂ j) λ where
        k (i = i0) → sq0 j (~ k)
        k (i = i1) → sq1 j (~ k)
        k (j = i0) → v k y
        k (j = i1) → u k (w i)
        k (k = i0) → sq i j

      fiber-paths : Path (fiber (coe A i1) y) (x0 , p0) (x1 , p1)
      fiber-paths i .fst = w i
      fiber-paths i .snd j = cb i (~ j)

      η : g (f x1) ＝ x1
      η i = hcomp (∂ i) λ where
        j (i = i0) → g (f x1)
        j (i = i1) → w j
        j (j = i0) → g (p1 i)

      φ : Square refl p1 (sym p0) (ap f (sym w))
      φ = tri.by-comp (sym p0) (ap f w) (sym p1) (Square.transpose cb)

      α : ap f η ＝ has-fiber A (f x1) .snd
      α i j = hcomp (∂ i ∨ ∂ j) λ where
        k (i = i0) → f (path-filler refl (ap g p1) w j k)
        k (i = i1) → has-fiber A (p1 (~ k)) .snd j
        k (j = i0) → f (g (p1 (i ∧ ~ k)))
        k (j = i1) → φ (~ k) (~ i)
        k (k = i0) → neutral-square (ap (f ∘ g) p1) p0 i j

  unit : ∀ {ℓ} (A : I → Type ℓ) (x : A i0)
       → transport (λ i → A (~ i)) (coe A i1 x) ＝ x
  unit A x = η A (coe A i1 x) (x , refl)

  counit : ∀ {ℓ} (A : I → Type ℓ) (y : A i1)
         → coe A i1 (op (λ i → A i) y) ＝ y
  counit A y = has-fiber A y .snd

  adj : ∀ {ℓ} (A : I → Type ℓ) (x : A i0)
      → ap (coe A i1) (unit A x) ＝ counit A (coe A i1 x)
  adj A x = α A (coe A i1 x) (x , refl)

  fiber-is-contr : ∀ {ℓ} (A : I → Type ℓ) (y : A i1)
                 → is-contr (fiber (coe A i1) y)
  fiber-is-contr A y .ctr = has-fiber A y
  fiber-is-contr A y .paths = fiber-paths A y

transportd : ∀ {ℓ} {A B : I → Type ℓ} (P : A i1 ＝ B i0)
           → {a : A i0} {b : A i1} → PathP A a b → B i1
transportd {B = B} P p  = transport (λ i → B i) (transport P (p i1))

to-pathp : ∀ {ℓ} {A : I → Type ℓ} {x : A i0} {y : A i1}
         → coe A i1 x ＝ y → PathP A x y
to-pathp {A} {x} p i = hcomp (∂ i) λ where
  j (i = i0) → x
  j (i = i1) → p j
  j (j = i0) → coe A i x

Path＝PathP : ∀ {ℓ} (P : I → Type ℓ) (p : P i0) (q : P i1)
           → Path (P i1) (transport (λ i → P i) p) q ＝ PathP P p q
Path＝PathP P p q i = PathP (λ j → P (~ i ∨ j)) (transport.filler (λ j → P j) p (~ i)) q

-- Turn a contractibility proof into an extension type, used in Prim.Equiv
-- and for Cubical HLevel proofs
is-contr→extend : ∀ {ℓ} {A : Type ℓ} → is-contr A
                → (i : I) (p : Partial i A) →  A [ i ↦ p ]
is-contr→extend contr i p = inS
  (hcomp (∂ i) λ where
      j (i = i1) → contr .paths (p 1=1) j
      j (i = i0) → contr .ctr
      j (j = i0) → contr .ctr)
{-# INLINE is-contr→extend #-}

extend→is-contr : ∀ {ℓ} {A : Type ℓ}
                → (∀ i (p : Partial i A) → A [ i ↦ p ])
                → is-contr A
extend→is-contr ex .ctr = outS (ex i0 λ ())
extend→is-contr ex .paths x i = outS (ex i (λ _ → x))

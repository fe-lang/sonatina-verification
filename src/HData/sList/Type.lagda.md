Swapped lists from:

https://arxiv.org/pdf/2110.05412

```agda
{-# OPTIONS --safe --erased-cubical #-}

module HData.sList.Type where

open import Prim.Prelude

infixr 8 _∷_

data sList {u} (A : Type u) : Type u where
  nil : sList A
  _∷_ : A → sList A → sList A
  swap : (x y : A) (xs : sList A) → (x ∷ y ∷ xs) ＝ (y ∷ x ∷ xs)
  trunc : is-set (sList A)

opaque instance
  H-Level-sList : ∀ {u} {A : Type u} → H-Level 2 (sList A)
  H-Level-sList .H-Level.has-hlevel = trunc

sList-ind : ∀ {u v} {A : Type u} (P : sList A → Type v)
          → P nil
          → (∀ x {xs} → P xs → P (x ∷ xs))
          → (∀ xs → is-prop (P xs))
          → (xs : sList A) → P xs
sList-ind P c _ _ nil = c
sList-ind P c a pprop (x ∷ xs) = a x (sList-ind P c a pprop xs)
sList-ind {v} {A} P c a pprop (swap x y xs i) =
  let
    g : (xs : sList A) → P xs
    g = sList-ind P c a pprop
  in is-prop→PathP (λ i → pprop (swap x y xs i))
       (a x (a y (g xs))) (a y (a x (g xs))) i
sList-ind {A} P c a pprop (trunc xs ys p q i j) =
  let
    g : (xs : sList A) → P xs
    g = sList-ind P c a pprop
  in is-prop→SquareP (λ k l → pprop (trunc xs ys p q k l))
       (λ i → g (p i)) (λ _ → g xs) (λ i → g (q i)) (λ i → g ys) i j

sList-append : ∀ {ℓ} {A : Type ℓ} → sList A → sList A → sList A
sList-append nil ys = ys
sList-append (x ∷ xs) ys = x ∷ (sList-append xs ys)
sList-append (swap x y xs i) ys = swap x y (sList-append xs ys) i
sList-append {A} (trunc xs ys p q i j) zs =
  trunc (sList-append xs zs) (sList-append ys zs)
    (λ i → sList-append (p i) zs)
    (λ i → sList-append (q i) zs) i j

sList-map : ∀ {u v} {A : Type u} {B : Type v}
          → (f : A → B) → sList A → sList B
sList-map {A = A} {(B)} f nil = nil
sList-map {A = A} {(B)} f (x ∷ xs) = f x ∷ sList-map f xs
sList-map {A = A} {(B)} f (swap x y xs i) = swap (f x) (f y) (sList-map f xs) i
sList-map {A = A} {(B)} f (trunc xs ys p q i j) =
  trunc (sList-map f xs) (sList-map f ys)
    (λ i → sList-map f (p i))
    (λ i → sList-map f (q i)) i j

instance
  Singleton-sList : Singleton (eff sList)
  Singleton-sList .Singleton.[_] = _∷ nil
  Singleton-sList .Singleton.[] = nil

  Map-sList : Map (eff sList)
  Map-sList .Map.map = sList-map

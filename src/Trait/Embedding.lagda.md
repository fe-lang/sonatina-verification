```agda
{-# OPTIONS --safe --erased-cubical #-}

module Trait.Embedding where

open import Prim.Prelude
open import Trait.Contr
open import Trait.Equiv
open import Trait.HLevel

open import Data.Path.Base

is-embedding : ∀ {u v} {A : Type u} {B : Type v} → (A → B) → Type _
is-embedding f = ∀ x → is-prop (fiber f x)

module _ {u v} {A : Type u} {B : Type v} (f : A → B) where
  injective : Type (u ⊔ v)
  injective = ∀ {x y} → f x ＝ f y → x ＝ y

  has-prop-fibers→injective : (∀ x → is-prop (fiber f x))
                           → injective
  has-prop-fibers→injective prop {x} {y} p = ap fst (prop (f y) (x , p) (y , refl))

  embedding-lemma : (∀ x → is-contr (fiber f (f x))) → is-embedding f
  embedding-lemma cffx y (x , p) q =
    is-contr→is-prop (subst is-contr (ap (fiber f) p) (cffx x)) (x , p) q

is-equiv→is-embedding
  : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} {f : A → B}
  → is-equiv f
  → is-embedding f
is-equiv→is-embedding eqv x = is-contr→is-prop (eqv .contr-map x)

is-equiv→injective : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} {f : A → B}
                   → is-equiv f → injective f
is-equiv→injective eqv = has-prop-fibers→injective (eqv-fun eqv)
  (is-equiv→is-embedding eqv)
-- _↪_ : ∀ {u v}  Type ℓ → Type ℓ₁ → Type _
-- A ↪ B = Σ[ f ∈ (A → B) ] is-embedding f

--injective :

```

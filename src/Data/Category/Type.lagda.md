```agda

{-# OPTIONS --safe --erased-cubical #-}

module Data.Category.Type where

open import Prim.Type
open import Prim.Pi
open import Prim.Data.Path
open import Prim.Data.Sigma
open import Prim.Equiv
open import Prim.Reasoning using (path-reasoning-syntax)

open import Trait.Category.Type public
open import Meta.Cut.Type public

record Category o h : Type₊ (o ⊔ h) where
  field
    Ob : Type o
    Hom : Ob → Ob → Type h
    seq : ∀ {x y z} → Hom x y → Hom y z → Hom x z
    assoc : ∀ {w x y z} (f : Hom w x) (g : Hom x y) (h : Hom y z)
          → seq f (seq g h) ＝ seq (seq f g) h
    is-cat : is-category Hom seq

  module _ (x : Ob) where open has-identity (is-cat x) public

  open is-category Hom seq is-cat
    (λ {x} f → assoc (idn x) (idn x) f)
    (λ {y = y} f → sym (assoc f (idn y) (idn y)))
    public

  instance
    Cut-Category : Hom-Cut Hom
    Cut-Category .Cut.seq = seq

  op : Category o h
  op .Ob = Ob
  op .Hom = flip Hom
  op .seq = flip seq
  op .assoc f g h = sym (assoc h g f)
  op .is-cat x .has-identity.idn = idn x
  op .is-cat x .has-identity.idn-idpt = idn-idpt x
  op .is-cat x .has-identity.idn-sec y = idn-retr x y
  op .is-cat x .has-identity.idn-retr y = idn-sec x y

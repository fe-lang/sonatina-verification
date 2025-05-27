```agda

{-# OPTIONS --safe --erased-cubical #-}

module Data.Category.Type where

open import Prim.Type
open import Prim.Interval
open import Lib.Pi
open import Trait.Contr
open import Data.Path.Type
open import Data.Sigma.Type
open import Trait.Equiv
open import Data.Path.Reasoning

open import Trait.Category.Type public
open import Meta.Cut public
open import Meta.Underlying public

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

open Category public

{-# DISPLAY Category.seq _ f g = f ∙ g #-}

Universe : ∀ u → Category (u ₊) u
Universe u .Category.Ob = Type u
Universe u .Category.Hom = λ A B → B → A
Universe u .Category.seq = funcomp
Universe u .Category.assoc f g h = refl
Universe u .Category.is-cat A .has-identity.idn = id
Universe u .Category.is-cat A .has-identity.idn-idpt = refl
Universe u .Category.is-cat A .has-identity.idn-sec B .contr-map x .ctr = x , refl
Universe u .Category.is-cat A .has-identity.idn-sec B .contr-map x .paths (y , p) i =
  p (~ i) , λ j → p (~ i ∨ j)
Universe u .Category.is-cat A .has-identity.idn-retr B .contr-map f .ctr = f , refl
Universe u .Category.is-cat A .has-identity.idn-retr B .contr-map f .paths (g , p) i =
  p (~ i) , λ j → p (~ i ∨ j)

instance
  Underlying-Category : ∀ {o h} → Underlying (Category o h)
  Underlying-Category {o} .Underlying.ℓ-underlying = o
  Underlying-Category .⌞_⌟ = Category.Ob

```agda
{-# OPTIONS --safe --erased-cubical #-}

module Lib.Base where

open import Prim.Type public
open import Prim.Interval.Core public
open import Prim.Pi public
open import Prim.Equiv public
open import Prim.Fiber public
open import Prim.Interval.Fill public
open import Prim.Reasoning public
open import Prim.Interval.Kan
  using (hcomp; hfill; path-comp)
  public

open import Prim.Data.Path public
open import Prim.Data.Contr public
open import Prim.Data.Sigma public
open import Prim.Data.Nat public
  hiding (_<_)

open import Data.Sum.Type public
open import Data.Empty.Type public
open import Data.Unit.Type public
open import Data.Dec.Type public
open import Data.Bool.Type public

open import Meta.Underlying public
open import Meta.Cut public

import Prim.Interval.Glue

```

Finally, we export `funext` here, as well as its inverse opperation `happly`

```

funext : ∀ {ℓ ℓ'} {A : Type ℓ} {B : A → Type ℓ'} {f g : (x : A) → B x}
       → ((x : A) → f x ＝ g x) → f ＝ g
funext p i x = p x i

funexti : ∀ {ℓ} {A : I → Type ℓ} {f g : (i : I) → A i}
       → ((i : I) → f i ＝ g i) → f ＝ g
funexti p i j = p j i

happly : ∀ {a b} {A : Type a} {B : A → Type b} {f g : (x : A) → B x}
       → f ＝ g → (x : A) → f x ＝ g x
happly p x i = p i x

```

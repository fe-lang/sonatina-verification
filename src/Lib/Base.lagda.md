```agda
{-# OPTIONS --safe --erased-cubical #-}

module Lib.Base where

open import Prim.Type public
open import Prim.Cubical public
open import Prim.Pi public
open import Prim.Equiv public
open import Prim.Fiber public
open import Prim.Reasoning public
open import Prim.Kan
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

import Prim.Glue
import Prim.Fill
module Fill = Prim.Fill

transport-filler : ∀ {ℓ} {A B : Type ℓ} (p : A ＝ B) (x : A)
                 → PathP (λ i → p i) x (transport p x)
transport-filler p x i = transp (λ j → p (i ∧ j)) (~ i) x

transport-refl : ∀ {ℓ} {A : Type ℓ} (x : A) → transport (λ _ → A) x ＝ x
transport-refl {A = A} x i = transp (λ i → A) i x


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


𝓙-refl : ∀ {ℓ ℓ'} {A : Type ℓ} (C : (x y : A) → x ＝ y → Type ℓ')
              → (c : (a : A) → C a a (λ i → a)) (x : A)
              → 𝓙 C c (λ i → x) ＝ c x
𝓙-refl C c x = transport-refl (c x)

```

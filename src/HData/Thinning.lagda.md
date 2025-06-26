```agda
{-# OPTIONS --safe --erased-cubical #-}

module HData.Thinning where

open import Prim.Prelude
open import Data.List
infixl 8 _:-_
infix 2 _⊑_

pattern _:-_ xs x = x ∷ xs

data _⊑_ {u} {A : Type u} : List A → List A → Type u where
  z : nil ⊑ nil
  here : ∀ {xs ys x} → xs ⊑ ys → xs :- x ⊑ ys :- x
  there : ∀ {xs ys x} → xs ⊑ ys → xs ⊑ ys :- x
  swap : ∀ x y xs ys → here ? ? y (there xs ys x) ＝ here ? ? (there ys xs )


```

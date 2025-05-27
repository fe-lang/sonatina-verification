```agda

{-# OPTIONS --safe --cubical-compatible #-}

module Data.List.Type where

open import Prim.Type

open import Data.Nat.Type

open import Agda.Builtin.List public renaming (_∷_ to infixr 40 _∷_)
open import Meta.Append public
open import Meta.Idiom public

append : ∀ {u} {A : Type u} → List A → List A → List A
append [] ys = ys
append (x ∷ xs) ys = x ∷ append xs ys

length : ∀ {u} {A : Type u} → List A → Nat
length [] = zero
length (x ∷ xs) = suc (length xs)

List-map : ∀ {u v} {A : Type u} {B : Type v} (f : A → B) → List A → List B
List-map f [] = []
List-map f (x ∷ xs) = f x ∷ List-map f xs

List-app : ∀ {u v} {A : Type u} {B : Type v}
         → List (A → B) → List A → List B
List-app [] as = []
List-app (f ∷ fs) [] = []
List-app (f ∷ fs) (x ∷ as) = f x ∷ List-app fs as

instance
  Append-List : ∀ {ℓ} {A : Type ℓ} → Append (List A)
  Append-List .Append.mempty = []
  Append-List .Append._++_ = append

  Idiom-List : Idiom (eff List)
  Idiom-List .Idiom.Map-idiom .Map.map = List-map
  Idiom-List .Idiom.pure = _∷ []
  Idiom-List .Idiom._<*>_ = List-app

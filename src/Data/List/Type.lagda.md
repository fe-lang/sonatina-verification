```agda

{-# OPTIONS --safe --cubical-compatible #-}

module Data.List.Type where

open import Prim.Type

open import Data.Nat.Type

open import Agda.Builtin.List public
  renaming (_∷_ to infixr 40 _∷_
           ; [] to nil )
open import Meta.Append public
open import Meta.Idiom public
open import Meta.Foldable public
open import Meta.Singleton

instance
  Singleton-List : Singleton (eff List)
  Singleton-List .Singleton.[_] = _∷ nil
  Singleton-List .Singleton.[] = nil

append : ∀ {u} {A : Type u} → List A → List A → List A
append nil ys = ys
append (x ∷ xs) ys = x ∷ append xs ys

length : ∀ {u} {A : Type u} → List A → Nat
length nil = zero
length (x ∷ xs) = suc (length xs)

List-map : ∀ {u v} {A : Type u} {B : Type v} (f : A → B) → List A → List B
List-map f nil = nil
List-map f (x ∷ xs) = f x ∷ List-map f xs

List-app : ∀ {u v} {A : Type u} {B : Type v}
         → List (A → B) → List A → List B
List-app nil as = nil
List-app (f ∷ fs) nil = nil
List-app (f ∷ fs) (x ∷ as) = f x ∷ List-app fs as

List-foldr : ∀ {u v} {A : Type u} {B : Type v}
           → (A → B → B) → B → List A → B
List-foldr h c nil = c
List-foldr h c (x ∷ xs) = h x (List-foldr h c xs)

instance
  Append-List : ∀ {ℓ} {A : Type ℓ} → Append (List A)
  Append-List .Append.mempty = nil
  Append-List .Append._++_ = append

  Idiom-List : Idiom (eff List)
  Idiom-List .Idiom.Map-idiom .Map.map = List-map
  Idiom-List .Idiom.pure = _∷ nil
  Idiom-List .Idiom._<*>_ = List-app

  Foldable-List : Foldable (eff List)
  Foldable-List .Foldable.foldr = List-foldr

{-# DISPLAY List-map = map #-}
{-# DISPLAY List-foldr = foldr #-}


data Listr {u} {A : Type u} : List A → Type u where
  nil : Listr nil
  snoc : {xs : List A} → Listr xs → (a : A) → Listr (xs ++ pure a)

```agda
{-# OPTIONS --safe --cubical-compatible #-}

module Data.Tree where

open import Prim.Type
open import Meta.Idiom
open import Meta.Foldable public

data Tree {u} (A : Type u) : Type u where
  leaf : A → Tree A
  node : Tree A → Tree A → Tree A

Tree-map : ∀ {u v} {A : Type u} {B : Type v}
         → (A → B) → Tree A → Tree B
Tree-map f (leaf x) = leaf (f x)
Tree-map f (node a b) = node (Tree-map f a) (Tree-map f b)

Tree-eval : ∀ {u v} {A : Type u} {B : Type v}
         → Tree (A → B) → Tree A → Tree B
Tree-eval (leaf f) = Tree-map f
Tree-eval (node t s) a = node (Tree-eval t a) (Tree-eval s a)

instance
  Idiom-Tree : Idiom (eff Tree)
  Idiom-Tree .Idiom.Map-idiom .Map.map = Tree-map
  Idiom-Tree .Idiom.pure = leaf
  Idiom-Tree .Idiom._<*>_ = Tree-eval

  Foldable-Tree : Foldable (eff Tree)
  Foldable-Tree .Foldable.foldr f b0 (leaf x) = f x b0
  Foldable-Tree .Foldable.foldr f b0 (node t s) = f {!!} {!!}

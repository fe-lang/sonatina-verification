```agda
{-# OPTIONS --safe --cubical-compatible #-}

module Data.LTree where

open import Prim.Type
open import Meta.Append
open import Meta.Idiom
open import Meta.Singleton

data LTree : Type where
  emp : LTree
  lf : LTree
  br : LTree → LTree → LTree

instance
  Append-LTree : Append LTree
  Append-LTree .Append.mempty = emp
  Append-LTree .Append._<>_ = br

data _≤_ : LTree → LTree → Type where
  instance emp-lf : emp ≤ lf
  br-left : ∀ {s t} → s ≤ t → s ≤ br s t
  br-right : ∀ {s t} → s ≤ t → s ≤ br t s

data Ptr : LTree → Type where
  here : Ptr lf
  ↙ : ∀ {s t} → Ptr s → Ptr (s <> t)
  ↘ : ∀ {s t} → Ptr t → Ptr (s <> t)

LVec : ∀ {u} → Type u → LTree → Type u
LVec A s = Ptr s → A

data BVec {u} (A : Type u) : LTree → Type u where
  here : A → BVec A lf
  ↙ : ∀ {s t} → A → BVec A s → BVec A (s <> t)
  ↘ : ∀ {s t} → A → BVec A t → BVec A (s <> t)

--singl-vec : ∀ {u} {A : Type u} → A → LVector A unit

LVec-map : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'}
         → (A → B) → {x : LTree} → LVec A x → LVec B x
LVec-map f {x} as = λ x → f (as x)

LVec-pure : ∀ {ℓ} {A : Type ℓ} {x : LTree} → A → LVec A x
LVec-pure a here = a
LVec-pure a (↙ p) = {!!}
LVec-pure a (↘ p) = {!!}

instance
  Idiom-LVector : ∀ {x : LTree} → Idiom (eff λ A → LVec A x)
  Idiom-LVector {(x)} .Idiom.Map-idiom .Map.map f as = LVec-map f as
  Idiom-LVector {(x)} .Idiom.pure = {!!}
  Idiom-LVector {(x)} .Idiom._<*>_ = {!!}

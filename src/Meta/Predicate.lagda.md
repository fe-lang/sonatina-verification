
```agda

{-# OPTIONS --safe --erased-cubical #-}

module Meta.Predicate where

open import Prim.Type
open import Data.Unit.Type
open import Meta.Underlying

infix -1 forall-syntax

forall-syntax : ∀ {u v} {X : Type u} → (X → Type v) → Type (u ⊔ v)
forall-syntax P = ∀ {a} → P a

syntax forall-syntax P = ∀∎ P

pred-syntax : ∀ {u v w} {X : Type u}
            → ((X → Type v) → (X → Type w)) → (X → Type v) → X → Type w
pred-syntax F Q x = F Q x

instance
  Underlying-Pred : ∀ {u v} {A : Type u} → Underlying (A → Type v)
  Underlying-Pred {u} {v} .Underlying.ℓ-underlying = u ⊔ v
  Underlying-Pred .Underlying.⌞_⌟ P = ∀ {x} → P x

Unit : ∀ {u} {A : Type u} → A → Type
Unit a = ⊤

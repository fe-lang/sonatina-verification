```agda
{-# OPTIONS --safe --erased-cubical #-}

module HData.sList.Scope where

open import Prim.Prelude
open import HData.sList.Type

record sKind {ℓ} (σ : Type ℓ) : Type ℓ where
  inductive
  field
    sort : σ
    scope : sList (sKind σ)

pattern _:-_ xs x = x ∷ xs

infixl 8 _:-_
infix 2 _↝_

data _↝_ {u} {A : Type u} : sList A → sList A → Type u where
  pop : ∀ a iz → iz :- a ↝ iz
  push : ∀ a iz → iz ↝ iz :- a
  goto : ∀ {iz} jz → iz ↝ jz

-- unit : ∀ {ℓ} {A : Type ℓ} (iz : sList A) → iz ⊑ iz
-- unit nil = singl nil
-- unit (iz :- x) = pop x iz iz (unit iz)
-- unit (swap x y iz i) = {!!}
-- unit (trunc iz iz₁ x y i i₁) = {!!}


-- ```

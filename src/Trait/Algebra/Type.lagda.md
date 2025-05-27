From the presentation in the paper "Algebraic Effects Meet Hoare Logic
in Cubical Agda" by Donnacha Oisín Kidney, Zhixuan Yang, and Nicolas Wu

```agda

{-# OPTIONS --safe --cubical-compatible #-}

module Trait.Algebra.Type where

open import Prim.Type
open import Data.Sigma.Type
open import Meta.Bracket

record Signature ℓ ℓ' : Type₊ (ℓ ⊔ ℓ') where
  constructor _◁_
  field
    Op : Type ℓ
    Ar : Op → Type ℓ'

open Signature public

instance
  Underlying-Signature : ∀ {u v} → Underlying (Signature u v)
  Underlying-Signature {u} .Underlying.ℓ-underlying = u
  Underlying-Signature .⌞_⌟ = Op

  -- Extension/semantics of signatures in `Type`
  ⟦⟧-Signature : ∀ {ℓ ℓ' u} → ⟦⟧-notation (Signature ℓ ℓ')
  ⟦⟧-Signature {ℓ} {ℓ'} {u} .⟦⟧-notation.lvl = ℓ ₊ ⊔ ℓ' ₊ ⊔ u ₊
  ⟦⟧-Signature {ℓ} {ℓ'} {u} .⟦⟧-notation.Sem = (X : Type u) → Type (ℓ ⊔ ℓ' ⊔ u)
  ⟦⟧-Signature .⟦⟧-notation.⟦_⟧ σ = λ X → Σ s ∶ Op σ , Ar σ s → X

-- The type of an F-algebra
_-Alg[_] : ∀ {o a} → Signature o a → Type (o ⊔ a) → Type (o ⊔ a)
F -Alg[ C ] = ⟦ F ⟧ C → C

-- -- Least fixpoint of signature-encoded functors
data μ {o a} (σ : Signature o a) : Type (o ⊔ a) where
  ⟨_⟩ : ⟦ σ ⟧ (μ σ) → μ σ

-- The following types are used in a context with an ambient signature,
-- which are to be introduced as an instance paramaterizing the module
-- utilizing them

-- module _ {o a} ⦃ σ : Signature o a ⦄ where
--   data Syntax (V : Type o) : Type (o ⊔ a) where
--     var : V → Syntax V
--     op : ⟦ σ ⟧ (Syntax V) → Syntax V

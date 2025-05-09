```agda

{-# OPTIONS --safe --cubical-compatible #-}

module Data.Container.Type where

open import Prim.Type
open import Prim.Data.Sigma

open import Control.Underlying

record Cont ℓ ℓ' : Type₊ (ℓ ⊔ ℓ') where
  constructor mk-cont
  field
    Sh : Type ℓ
    Pos : Sh → Type ℓ'

open Cont public

pos-syntax : ∀ {ℓ ℓ'} → (S : Cont ℓ ℓ') → Sh S → Type ℓ'
pos-syntax S = Pos S

syntax pos-syntax S s = ∣ s ∶ S ∣

instance
  cont-Underlying : ∀ {u v} → Underlying (Cont u v)
  cont-Underlying {u} {v} .Underlying.lv = u
  cont-Underlying .Underlying.⌞_⌟ S = Sh S

-- Extension/semantics of containers in `Type`
-- ⟦_⟧ : ∀ {ℓ ℓ' u} → Cont ℓ ℓ' → Type u → Type (ℓ ⊔ ℓ' ⊔ u)
-- ⟦_⟧ {ℓ} {ℓ'} σ X = Σ s ∶ ∣ σ ∣ₛ , ∥ s ∶ σ ∥ₛ → X

-- -- Least fixpoint of signature-encoded functors
-- data μ {ℓ ℓ'} (σ : Cont ℓ ℓ') : Type (ℓ ⊔ ℓ') where
--   ⟨_⟩ : ⟦ σ ⟧ (μ σ) → μ σ

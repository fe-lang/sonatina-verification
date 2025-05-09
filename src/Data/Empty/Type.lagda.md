```agda

{-# OPTIONS --safe --cubical-compatible #-}

module Data.Empty.Type where

open import Prim.Type

infixl 6 ¬_ ¬¬_ ¬¬¬_

data 𝟘 {ℓ} : Type ℓ where

𝟘-ind : ∀ {u v} (P : 𝟘 {u} → Type v) (e : 𝟘 {u}) → P e
𝟘-ind P ()

𝟘-rec : ∀ {u v} {A : Type v} → 𝟘 {u} → A
𝟘-rec {A = A} = 𝟘-ind (λ _ → A)
syntax 𝟘-rec = absurd

instance
  void : ∀ {ℓ} ⦃ e : 𝟘 {ℓ} ⦄ → 𝟘 {0ℓ}
  void ⦃ e ⦄ = absurd e

⊥ : Type
⊥ = 𝟘

¬_ ¬¬_ ¬¬¬_ is-empty : ∀ {u} → Type u → Type u
¬_ A = A → ⊥
¬¬ A = ¬ (¬ A)
¬¬¬ A = ¬ (¬ (¬ A))
is-empty = ¬_

contra : ∀ {ℓ ℓ'} {P : Type ℓ} {Q : Type ℓ'} → (P → Q) → ¬ Q → ¬ P
contra pq nq p = nq (pq p)

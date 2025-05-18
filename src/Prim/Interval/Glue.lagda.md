```agda

{-# OPTIONS --cubical --safe --no-sized-types --no-guardedness #-}

module Prim.Interval.Glue where

open import Prim.Type using ( Type )
open import Prim.Interval.Core using ( I; Partial; PartialP )

open import Prim.Equiv

primitive
  primGlue    : ∀ {ℓ ℓ'} (A : Type ℓ) {φ : I}
    → (T : Partial φ (Type ℓ')) → (e : PartialP φ (λ o → T o ≃ A))
    → Type ℓ'
  prim^glue   : ∀ {ℓ ℓ'} {A : Type ℓ} {φ : I}
    → {T : Partial φ (Type ℓ')} → {e : PartialP φ (λ o → T o ≃ A)}
    → (t : PartialP φ T) → (a : A) → primGlue A T e
  prim^unglue : ∀ {ℓ ℓ'} {A : Type ℓ} {φ : I}
    → {T : Partial φ (Type ℓ')} → {e : PartialP φ (λ o → T o ≃ A)}
    → primGlue A T e → A

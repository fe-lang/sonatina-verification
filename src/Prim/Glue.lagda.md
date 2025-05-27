```agda

{-# OPTIONS --cubical --safe --no-sized-types --no-guardedness #-}

module Prim.Glue where

open import Prim.Type using ( Type )
open import Data.Sigma.Type
open import Prim.Interval
open import Prim.HCompU

open import Trait.Equiv

private primitive
  primGlue    : ∀ {ℓ ℓ'} (A : Type ℓ) {φ : I}
    → (T : Partial φ (Type ℓ')) → (e : PartialP φ (λ o → T o ≃ A))
    → Type ℓ'
  prim^glue   : ∀ {ℓ ℓ'} {A : Type ℓ} {φ : I}
    → {T : Partial φ (Type ℓ')} → {e : PartialP φ (λ o → T o ≃ A)}
    → PartialP φ T → A → primGlue A T e
  prim^unglue : ∀ {ℓ ℓ'} {A : Type ℓ} {φ : I}
    → {T : Partial φ (Type ℓ')} → {e : PartialP φ (λ o → T o ≃ A)}
    → primGlue A T e → A

open import Prim.Kan

Glue : ∀ {ℓ ℓ'} (A : Type ℓ) {φ : I}
     → (Te : Partial φ (Σ T ∶ Type ℓ' , (T ≃ A))) → Type ℓ'
Glue {ℓ'} A {φ} Te = primGlue A tys eqvs where
  tys : Partial φ (Type _)
  tys (φ = i1) = Te 1=1 .fst

  eqvs : PartialP φ (λ .o → tys _ ≃ A)
  eqvs (φ = i1) = Te 1=1 .snd

```agda
{-# OPTIONS --safe --erased-cubical #-}

module Meta.Invariant where

open import Prim.Type
open import Trait.Equiv
open import Data.Unit.Type
open import Data.Empty.Type
open import Data.Sigma.Type
open import Data.Sum.Type
open import Meta.Idiom
open import Meta.Alt

record Invariant (M : Effect) : Typeω where
  private module M = Effect M
  field
    invmap
      : ∀ {ℓ} {ℓ′} {A : Type ℓ} {B : Type ℓ′}
      → (A → B) → (B → A) → M.₀ A → M.₀ B

open Invariant ⦃ ... ⦄ public

_<≃>_
  : ∀ {ℓ ℓ'} {M : Effect} ⦃ _ : Invariant M ⦄ {A : Type ℓ} {B : Type ℓ'}
  → A ≃ B → M .Effect.₀ A → M .Effect.₀ B
_<≃>_ f = invmap (Equiv.to f) (Equiv.from f)

record Monoidal (M : Effect) : Typeω where
  private module M = Effect M
  field
    ⦃ Invariant-monoidal ⦄ : Invariant M
    munit : M.₀ ⊤
    _<,>_
      : ∀ {ℓ} {ℓ′} {A : Type ℓ} {B : Type ℓ′}
      → M.₀ A → M.₀ B → M.₀ (A × B)

  infixl 4 _<,>_

record Alternative (M : Effect) : Typeω where
  private module M = Effect M
  field
    ⦃ Invariant-alternative ⦄ : Invariant M
    empty : M.₀ ⊥
    _<+>_
      : ∀ {ℓ} {ℓ′} {A : Type ℓ} {B : Type ℓ′}
      → M.₀ A → M.₀ B → M.₀ (A ⊎ B)

  infixl 3 _<+>_

open Monoidal ⦃ ... ⦄ public
open Alternative ⦃ ... ⦄ public

instance
  Invariant-Map : ∀ {M : Effect} → ⦃ Map M ⦄ → Invariant M
  Invariant-Map .Invariant.invmap f _ = f <$>_
  {-# OVERLAPPABLE Invariant-Map #-}

  Monoidal-Idiom : ∀ {M : Effect} → ⦃ Idiom M ⦄ → Monoidal M
  Monoidal-Idiom .Monoidal.munit = pure tt
  Monoidal-Idiom .Monoidal._<,>_ ma mb = _,_ <$> ma <*> mb
  {-# OVERLAPPABLE Monoidal-Idiom #-}

  Alternative-Alt : ∀ {M : Effect} → ⦃ Map M ⦄ → ⦃ Alt M ⦄ → Alternative M
  Alternative-Alt .Alternative.empty = fail
  Alternative-Alt .Alternative._<+>_ ma mb = inl <$> ma <|> inr <$> mb
  {-# INCOHERENT Alternative-Alt #-}

```

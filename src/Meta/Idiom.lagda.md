
```agda

{-# OPTIONS --safe --cubical-compatible #-}

module Meta.Idiom where

open import Prim.Type
open import Data.Unit.Type
open import Data.Sigma.Type
open import Data.Bool.Type
open import Meta.Underlying

record Map (M : Effect) : Typeω where
  private module M = Effect M
  field
    map : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} → (A → B) → M.₀ A → M.₀ B

open Map ⦃ ... ⦄ public

record Idiom (M : Effect) : Typeω where
  private module M = Effect M
  field
    ⦃ Map-idiom ⦄ : Map M
    pure  : ∀ {ℓ} {A : Type ℓ} → A → M.₀ A
    _<*>_ : ∀ {ℓ} {ℓ'} {A : Type ℓ} {B : Type ℓ'} → M.₀ (A → B) → M.₀ A → M.₀ B

  infixl 4 _<*>_

open Idiom ⦃ ... ⦄ public

infixl 4 _<$>_ _<&>_

_<$>_ : ∀ {ℓ ℓ'} {M : Effect} ⦃ _ : Map M ⦄ {A : Type ℓ} {B : Type ℓ'}
      → (A → B) → M .Effect.₀ A → M .Effect.₀ B
f <$> x = map f x

_<$_ : ∀ {ℓ ℓ'} {M : Effect} ⦃ _ : Map M ⦄ {A : Type ℓ} {B : Type ℓ'}
      → B → M .Effect.₀ A → M .Effect.₀ B
c <$ x = map (λ _ → c) x

_<&>_ : ∀ {ℓ ℓ'} {M : Effect} ⦃ _ : Map M ⦄ {A : Type ℓ} {B : Type ℓ'}
      → M .Effect.₀ A → (A → B) → M .Effect.₀ B
x <&> f = map f x

module _
  {M N : Effect} (let module M = Effect M; module N = Effect N) ⦃ _ : Map M ⦄ ⦃ _ : Map N ⦄
  {ℓ} {ℓ'} {A : Type ℓ} {B : Type ℓ'}
  where
  _<<$>>_ : (A → B) → M.₀ (N.₀ A) → M.₀ (N.₀ B)
  f <<$>> a = (f <$>_) <$> a

  _<<&>>_ : M.₀ (N.₀ A) → (A → B) → M.₀ (N.₀ B)
  x <<&>> f = f <<$>> x

when : ∀ {M : Effect} (let module M = Effect M) ⦃ app : Idiom M ⦄
     → Bool → M.₀ ⊤ → M.₀ ⊤
when true  t = t
when false _ = pure tt

unless : ∀ {M : Effect} (let module M = Effect M) ⦃ app : Idiom M ⦄
       → Bool → M.₀ ⊤ → M.₀ ⊤
unless false t = t
unless true  _ = pure tt

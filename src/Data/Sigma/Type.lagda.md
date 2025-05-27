```agda

{-# OPTIONS --safe --cubical-compatible #-}

module Data.Sigma.Type where

open import Prim.Type using (Type; _⊔_)
open import Meta.Underlying public
open import Meta.Operator public

infix 5 Σ-syntax

```

Import the Sigma type from Agda.Builtin. We'll useTopology's
notation because its far more convenient. We can use textbook style
notation if we want to annotate the type name with a syntax
declaration.

```
open import Agda.Builtin.Sigma public
  renaming ( Σ to Sigma
           ; _,_ to infixr 4 _,_ )
  using ( fst; snd; module Σ ) -- keep the module the same name, it works

Σ : ∀ {ℓ ℓ'} {A : Type ℓ} → (A → Type ℓ') → Type (ℓ ⊔ ℓ')
Σ {A = A} B = Sigma A B
{-# INLINE Σ #-}
{-# INLINE _,_ #-}

{-# DISPLAY Sigma A B = Σ B #-}

Pair : ∀ {ℓ ℓ'} → Type ℓ → Type ℓ' → Type (ℓ ⊔ ℓ')
Pair A B = Sigma A (λ _ → B)

Σ-syntax : ∀ {ℓ ℓ'} {A : Type ℓ} ⦃ _ : Underlying A ⦄
         → (X : A) (F : ⌞ X ⌟ → Type ℓ') → Type _
Σ-syntax X F = Sigma ⌞ X ⌟ F
syntax Σ-syntax A (λ x → M) = Σ x ∶ A , M
{-# DISPLAY Σ-syntax _ B = Σ B #-}

instance
  Σ-instance : ∀ {ℓ ℓ'} {A : Type ℓ} {B : A → Type ℓ'}
             → ⦃ x : A ⦄ ⦃ y : B x ⦄ → Σ B
  Σ-instance ⦃ x ⦄ .fst = x
  Σ-instance ⦃ y ⦄ .snd = y

  Times-Pair : ∀ {u v} → Times (λ (A : Type u) (B : Type v) → Type (u ⊔ v))
  Times-Pair .Times._×_ = Pair
  {-# DISPLAY Pair = _×_ #-}

  Underlying-Σ : ∀ {ℓ ℓ'} {A : Type ℓ} {B : A → Type ℓ'}
               → ⦃ ua : Underlying A ⦄
               → Underlying (Σ B)
  Underlying-Σ ⦃ ua ⦄ .ℓ-underlying = ua .ℓ-underlying
  Underlying-Σ .⌞_⌟ x = ⌞ x .fst ⌟

diag : ∀ {ℓ} {A : Type ℓ} → A → A × A
diag a = a , a

swap : ∀ {u v} {A : Type u} {B : Type v} → A × B → B × A
swap (a , b) = b , a

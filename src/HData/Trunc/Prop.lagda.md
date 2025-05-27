We'll define the basic types for Propositional and Set truncation
in this module

```agda

{-# OPTIONS --safe --erased-cubical #-}

module HData.Trunc.Prop where

open import Prim.Type
open import Prim.Interval
open import Data.Nat.Type
open import Data.Path.Type
open import Trait.HLevel.Base

data ∥_∥ {ℓ} (A : Type ℓ) : Type ℓ where
  inc : A → ∥ A ∥
  squash : is-prop ∥ A ∥

Pt-ind : ∀ {ℓ ℓ'} {A : Type ℓ} (P : ∥ A ∥ → Type ℓ')
         → (∀ x → is-prop (P x))
         → (∀ x → P (inc x))
         → (x : ∥ A ∥) → P x
Pt-ind P pprop f (inc x) = f x
Pt-ind P pprop f (squash x y i) =
  is-prop→PathP (λ j → pprop (squash x y j)) (Pt-ind P pprop f x) (Pt-ind P pprop f y) i

Pt-ind-β : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'}
         → (P : ∥ A ∥ → Type ℓ')
         → (pprop : ∀ x → is-prop (P x))
         → (base : ∀ x → P (inc x))
         → (x : ∥ A ∥) (p : P x) → Pt-ind P pprop base x ＝ p
Pt-ind-β P pprop base x p = pprop x (Pt-ind P pprop base x) p

Pt-map : ∀ {ℓ ℓ'} {A : Type ℓ}  {B : Type ℓ'} → (A → B) → ∥ A ∥ → ∥ B ∥
Pt-map {A} {B} f = Pt-ind (λ U → ∥ B ∥) (λ _ → squash) (λ x → inc (f x))

data ∥_∥₀ {ℓ} (A : Type ℓ) : Type ℓ where
  inc    : A → ∥ A ∥₀
  squash : is-set ∥ A ∥₀

St-ind : ∀ {ℓ ℓ'} {A : Type ℓ} (P : ∥ A ∥₀ → Type ℓ')
       → (∀ x → is-set (P x))
       → (∀ x → P (inc x))
       → (x : ∥ A ∥₀) → P x
St-ind P bset binc (inc x) = binc x
St-ind {A} P bset binc (squash x y p q i j) =
  let
    g : (x₁ : ∥ A ∥₀) → P x₁
    g = St-ind P bset binc
  in
    is-set→SquareP (λ i j → bset (squash x y p q i j))
      (λ i → g (p i)) (λ _ → g x) (λ i → g (q i)) (λ i → g y) i j

St-map : ∀ {ℓ ℓ'} {A : Type ℓ}  {B : Type ℓ'} → (A → B) → ∥ A ∥₀ → ∥ B ∥₀
St-map {A} {B} f = St-ind (λ _ → ∥ B ∥₀) (λ _ → squash) (λ x → inc (f x))

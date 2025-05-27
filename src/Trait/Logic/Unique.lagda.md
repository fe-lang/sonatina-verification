```agda
{-# OPTIONS --safe --erased-cubical #-}

module Trait.Logic.Unique where

open import Prim.Type
open import Prim.Interval
open import Data.Path.Type
open import Trait.HLevel.Base
open import Trait.Logic.Exists

open import Data.Sigma.Type public
open import Trait.Contr public

infixr 5 ∃!-syntax

-- Unique existence
∃! : ∀ {u v} {A : Type u} (B : A → Type v) → Type (u ⊔ v)
∃! B = is-contr (Σ B)

unique : ∀ {u v} {A : Type u} {B : A → Type v} → is-prop (Σ B) → Σ B → ∃! B
unique = contractible

∃!-syntax : ∀ {ℓ ℓ'} {A : Type ℓ} ⦃ _ : Underlying A ⦄
          → (X : A) (F : ⌞ X ⌟ → Type ℓ') → Type _
∃!-syntax X F = is-contr (Sigma ⌞ X ⌟ F)
syntax ∃!-syntax A (λ x → M) = ∃! x ∶ A , M
{-# DISPLAY ∃!-syntax _ B = ∃! B #-}

unique→exists : ∀ {u v} {A : Type u} {B : A → Type v}
              → ∃! B → ∃ B
unique→exists ub = inc (ub .ctr)

exists→unique : ∀ {u v} {A : Type u} {B : A → Type v}
              → is-prop A → (∀ x → is-prop (B x)) → ∃ B → ∃! B
exists→unique {B = B} aprop bprop ex = Pt-ind (λ _ → ∃! B) (λ _ → is-contr-is-prop (Σ B)) φ ex where
  α : Σ B
  α = Pt-ind {!!} {!!} {!!} ex

  φ : Σ B → ∃! B
  φ z .ctr = z
  φ z .paths w i .fst = aprop (z .fst) (w .fst) i
  φ z .paths w i .snd = {!!}

∃!-map : ∀ {u v w} {A : Type u} {P : A → Type v} {Q : A → Type w}
       → (f : Σ P → Σ Q) → is-prop (Σ Q) → ∃! P → ∃! Q
∃!-map {P} {Q} f fprop = λ z → f (z .ctr) , fprop (f (z .ctr))

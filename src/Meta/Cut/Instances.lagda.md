```agda
{-# OPTIONS --safe --erased-cubical #-}

module Meta.Cut.Instances where

open import Prim.Type
open import Prim.Data.Path using (Path)
open import Prim.Interval.Kan using (path-comp)

open import Meta.Cut.Type
open import Data.Category.Type

instance
  Cut-funcomp : ∀ {u v w} {B : Type v} {C : B → Type w}
    → Cut (λ (A : Type u) → A → B)
          (λ _ → (b : B) → C b)
          (λ (A : Type u) f → ∀ x → C (f x))
  Cut-funcomp .Cut.seq f g x = g (f x)
  {-# INCOHERENT Cut-funcomp #-}

  Cut-pathcomp : ∀ {u} {A : Type u} → Hom-Cut (Path A)
  Cut-pathcomp .Cut.seq = path-comp

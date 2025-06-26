```agda
{-# OPTIONS --safe --cubical-compatible #-}

module Meta.Display where

open import Prim.Type
open import Meta.Object

record Display (C : Quiver) (F : Effect) : Typeω where
  no-eta-equality
  constructor disp
  private module C = Quiver C
          module F = Effect F

  Ob[_] = F.₀
  field
    {ℓ-disp} : Level → Level → Level → Level
    Hom[_] : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'}
           → C.Hom A B → Ob[ A ] → Ob[ B ]
           → Type (ℓ-disp ℓ ℓ' (C.ℓ-hom ℓ ℓ'))

private module _ {ℓ ℓ'} {Ob : Type ℓ} (_≤_ : Ob → Ob → Type ℓ') where
  Cat : Display (quiver (λ _ _ → Ob)) (eff (λ _ → Ob))
  Cat = disp λ _ → _≤_




```

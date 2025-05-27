```agda
{-# OPTIONS --safe --cubical-compatible #-}

module Meta.Bracket where

open import Prim.Type

record ⟦⟧-notation {ℓ} (A : Type ℓ) : Typeω where
  constructor brackets
  field
    {lvl} : Level
    Sem : Type lvl
    ⟦_⟧ : A → Sem

open ⟦⟧-notation ⦃...⦄ using (⟦_⟧) public
{-# DISPLAY ⟦⟧-notation.⟦_⟧ _ x = ⟦ x ⟧ #-}

```

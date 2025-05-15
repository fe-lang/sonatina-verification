```agda

{-# OPTIONS --safe --cubical-compatible #-}

module Prim.Data.Sigma where

open import Prim.Type using (Type; _⊔_)

infixr 5 _×_

```

Import the Sigma type from Agda.Builtin. We'll useTopology's
notation because its far more convenient. We can use textbook style
notation if we want to annotate the type name with a syntax
declaration.

```
open import Agda.Builtin.Sigma public
  renaming ( Σ to Sigma )
  using ( _,_; fst; snd; module Σ ) -- keep the module the same name, it works

Σ : ∀ {ℓ ℓ'} {A : Type ℓ} → (A → Type ℓ') → Type (ℓ ⊔ ℓ')
Σ {A = A} B = Sigma A B
{-# INLINE Σ #-}
{-# INLINE _,_ #-}

{-# DISPLAY Sigma A B = Σ B #-}

_×_ : ∀ {ℓ ℓ'} → Type ℓ → Type ℓ' → Type (ℓ ⊔ ℓ')
A × B = Sigma A (λ _ → B)

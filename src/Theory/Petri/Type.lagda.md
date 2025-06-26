```agda
{-# OPTIONS --safe --erased-cubical #-}

module Theory.Petri.Type where

open import Prim.Prelude
open import HData.sList

record Petri-net u v : Type (u ₊ ⊔ v ₊) where
  field
    S : Type u
    S-is-set : is-set S
    T : sList S → sList S → Type v -- Transitions
    ⦃ Petri-net-composable ⦄ : Composable (hom T)

  seq : {xs ys zs : sList S} → T xs ys → T ys zs → T xs zs
  seq = Composable.seq Petri-net-composable

instance
  Underlying-Petri-Net : ∀ {o e} → Underlying (Petri-net o e)
  Underlying-Petri-Net {o} .Underlying.ℓ-underlying = o
  Underlying-Petri-Net .Underlying.⌞_⌟ = Petri-net.S

record Petri-net-hom {o₁ o₂ v₁ v₂}
  (M : Petri-net o₁ v₁)
  (N : Petri-net o₂ v₂)
  : Type {!!}
  where
  private module M = Petri-net M
  private module N = Petri-net N

  field
    F₀ : ⌞ M ⌟ → ⌞ N ⌟





```

```agda
{-# OPTIONS --safe --erased-cubical #-}

module Theory.Syntax where

open import Lib.Base hiding (_+_)

propext : ∀ {u v} {P Q : Type u}
        → is-prop P → is-prop Q
        → (P → Q) → (Q → P) → P ＝ Q
propext pp qq f g = {!!}

_+_ : ∀ {u v} → Ω u → Ω v → Ω (u ⊔ v)
(P + Q) .Ω.₀ = Ω.₀ P ⊎ Ω.₀ Q
_+_ {(u)} {(v)} (P , pprop) (Q , qprop) .Ω.₁ s1 s2 = {!!}
  where
  -- pp : A → Type u
  -- pp = ?
  -- qq : B → Type v
  -- qq = ?
  A : P ⊎ Q → Type (u ⊔ v)
  A (inl a) = inl a ＝ s2
  A (inr b) = inr b ＝ s2

  φ : {!!}
  φ = match s1
    ∣ p => {!!}
    ∣ q => {!!}
    ∈ A

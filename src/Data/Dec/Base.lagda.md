```agda
{-# OPTIONS --safe --erased-cubical #-}

module Data.Dec.Base where

open import Prim.Base
open import Data.Irr
open import Data.Bool.Base
open import Data.Path.Type


open import Data.Dec.Type public

module _ {ℓ} {P : Type ℓ} where
  ⌊_⌋ : Dec P → Bool
  ⌊ yes _ ⌋ = true
  ⌊ no  _ ⌋ = false

  True : Dec P → Type
  True Q = Tt ⌊ Q ⌋

  False : Dec P → Type
  False Q = Tt (not ⌊ Q ⌋)

  -- Gives a witness to the "truth".

  witness : {Q : Dec P} → True Q → P
  witness {Q = yes p} _  = p
  witness {Q = no  _} ()

  -- Establishes a "truth", given a witness.

  has-witness : {Q : Dec P} → P → True Q
  has-witness {Q = yes p} = const _
  has-witness {Q = no ¬p} = ¬p

  -- Variants for False.

  negative : {Q : Dec P} → False Q → ¬ P
  negative {Q = yes _}  ()
  negative {Q = no  ¬p} _  = ¬p

  has-negation : {Q : Dec P} → ¬ P → False Q
  has-negation {Q = yes p} = flip _$_ p
  has-negation {Q = no ¬p} = const _

module _ {p} {P : Type p} where

  From-yes : Dec P → Type p
  From-yes (yes _) = P
  From-yes (no  _) = Lift p ⊤

  from-yes : (p : Dec P) → From-yes p
  from-yes (yes p) = p
  from-yes (no  _) = _

  From-no : Dec P → Type p
  From-no (no  _) = ¬ P
  From-no (yes _) = Lift p ⊤

  from-no : (p : Dec P) → From-no p
  from-no (no ¬p) = ¬p
  from-no (yes _) = _

module _ {ℓ} {P : Type ℓ} where
  dec-yes : (p? : Dec P) → P → Σ p ∶ P ,  (p? ＝ yes p)
  dec-yes (yes p) q = p , refl
  dec-yes (no ¬p) p = 𝟘-rec (¬p p)

  dec-no : (p? : Dec P) → ¬ P → Σ ¬p ∶ ¬ P , (p? ＝ no ¬p)
  dec-no (yes p) ¬p  = ¬p , 𝟘-rec (¬p p)
  dec-no (no ¬p′) ¬p = ¬p′ , refl

  -- dec-yes-irr : (p? : Dec P) → Irr P → (p : P) → p? ＝ yes p
  -- dec-yes-irr p? irr p with dec-yes p? p
  -- dec-yes-irr p? irr p | p' , eq = eq ∙ ap yes λ i → {!!}

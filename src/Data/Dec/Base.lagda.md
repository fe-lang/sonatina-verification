```agda
{-# OPTIONS --safe --cubical-compatible #-}

module Data.Dec.Base where

open import Prim.Type
open import Prim.Pi
open import Prim.Data.Sigma
open import Data.Bool.Base
open import Data.Empty.Type
open import Data.Dec.Type
open import Data.Unit.Type

module _ {ℓ} {P : Type ℓ} where
  ⌊_⌋ : Dec P → Bool
  ⌊ yes _ ⌋ = true
  ⌊ no  _ ⌋ = false

  True : Dec P → Type
  True Q = Tt ⌊ Q ⌋

  False : Dec P → Type
  False Q = Tt (not ⌊ Q ⌋)

  -- Gives a witness to the "truth".

  toWitness : {Q : Dec P} → True Q → P
  toWitness {Q = yes p} _  = p
  toWitness {Q = no  _} ()

  -- Establishes a "truth", given a witness.

  fromWitness : {Q : Dec P} → P → True Q
  fromWitness {Q = yes p} = const _
  fromWitness {Q = no ¬p} = ¬p

  -- Variants for False.

  toWitnessFalse : {Q : Dec P} → False Q → ¬ P
  toWitnessFalse {Q = yes _}  ()
  toWitnessFalse {Q = no  ¬p} _  = ¬p

  fromWitnessFalse : {Q : Dec P} → ¬ P → False Q
  fromWitnessFalse {Q = yes p} = flip _$_ p
  fromWitnessFalse {Q = no ¬p} = const _

  -- If a decision procedure returns "yes", then we can extract the
  -- proof using from-yes.

module _ {p} {P : Type p} where

  From-yes : Dec P → Type p
  From-yes (yes _) = P
  From-yes (no  _) = Lift p ⊤

  from-yes : (p : Dec P) → From-yes p
  from-yes (yes p) = p
  from-yes (no  _) = _

-- If a decision procedure returns "no", then we can extract the proof
-- using from-no.

  From-no : Dec P → Type p
  From-no (no  _) = ¬ P
  From-no (yes _) = Lift p ⊤

  from-no : (p : Dec P) → From-no p
  from-no (no ¬p) = ¬p
  from-no (yes _) = _

------------------------------------------------------------------------
-- Result of decidability

module _ {ℓ} {P : Type ℓ} where
  -- dec-yes : (p? : Dec P) → P → ∃ (λ p′ → p?) ≡ yes p′
  -- dec-yes (yes p′) p = p′ , refl
  -- dec-yes (no ¬p) p = ⊥-elim (¬p p)

  -- dec-no : (p? : Dec P) → ¬ P → ∃ λ ¬p′ → p? ≡ no ¬p′
  -- dec-no (yes p) ¬p  = ¬p , ⊥-elim (¬p p)
  -- dec-no (no ¬p′) ¬p = ¬p′ , refl

  -- dec-yes-irr : (p? : Dec P) → Irrelevant P → (p : P) → p? ≡ yes p
  -- dec-yes-irr p? irr p with dec-yes p? p
  -- ... | p′ , eq rewrite irr p p′ = eq
  -- ```

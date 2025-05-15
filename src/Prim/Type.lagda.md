```agda
{-# OPTIONS --safe --cubical-compatible #-}

module Prim.Type where

open import Agda.Primitive public
  using ( SSet
        ; SSetω
        ; LevelUniv
        ; Level )
  renaming ( Prop  to DIProp
           ; Set   to Type
           ; Setω  to Typeω
           ; _⊔_ to infixl 6 _⊔_
           ; lsuc to infixr 7 _₊
           ; lzero to 0ℓ )

1ℓ : Level
1ℓ = 0ℓ ₊

level-of : ∀ {ℓ} {A : Type ℓ} → A → Level
level-of {ℓ} _ = ℓ

Type₊ : ∀ ℓ → Type (ℓ ₊ ₊)
Type₊ ℓ = Type (ℓ ₊)

record Lift {u} ℓ (A : Type u) : Type (u ⊔ ℓ) where
  constructor lift
  field
    lower : A

open Lift public

id : ∀ {u} {A : Type u} → A → A
id = λ x → x
{-# INLINE id #-}

id-of : ∀ {u} (A : Type u) → A → A
id-of A = λ x → x
{-# INLINE id #-}

const : ∀ {u v} {A : Type u} {B : Type v} → A → B → A
const a ._ = a
{-# INLINE const #-}

rconst : ∀ {u v} {A : Type u} {B : Type v} → A → B → B
rconst ._ b = b
{-# INLINE rconst #-}

funcomp : ∀ {u v w} {A : Type u} {B : Type v} {C : B → Type w}
     → ((y : B) → C y) → (f : A → B) (x : A) → C (f x)
funcomp g f = λ x → g (f x)
{-# INLINE funcomp #-}

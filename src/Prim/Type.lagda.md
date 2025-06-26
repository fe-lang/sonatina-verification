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

record Effect : Typeω where
  constructor eff
  field
    {adj} : Level → Level
    ₀ : ∀ {ℓ} → Type ℓ → Type (adj ℓ)

record Quiver : Typeω where
  constructor quiver
  field
    {ℓ-hom} : Level → Level → Level
    Hom : ∀ {s t} → Type s → Type t → Type (ℓ-hom s t)

Λ-syntax : {M : Effect} (let module M = Effect M)
         → (∀ {u} (A : Type u) → A → M.₀ A)
         → ∀ {u} {A : Type u} → A → M.₀ A
Λ-syntax f {A} = f A
{-# INLINE Λ-syntax #-}
syntax Λ-syntax (λ A → B) = Λ A ∎ B

id : ∀ {u} {A : Type u} → A → A
id = Λ A ∎ λ (x : A) → x
{-# INLINE id #-}

idf : ∀ {u} (A : Type u) → A → A
idf A = λ x → x
{-# INLINE idf #-}

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

infixr 8 Λ-syntax

∂-syntax : {adj : Level → Level} {F : ∀ {u} → Type u → Type (adj u)}
         → (∀ {u} (A : Type u) → A → F A)
         → ∀ {u} {A : Type u} → A → F A
∂-syntax f {A} = f A

syntax ∂-syntax (λ A → B) = Λ A ∎ B
infixr 8 ∂-syntax

```agda

{-# OPTIONS --safe --cubical-compatible #-}

module Prim.Pi where

open import Prim.Type

-- This is the one Control module we'll allow in Prim due to how fundamental
-- function composition is, and we want it as soon as possible
open import Trait.Cut public

infixr -1 _$_
infixl -1 _&_

infix -1 pi-syntax

Π : ∀ {u v} {A : Type u} (B : A → Type v) → Type (u ⊔ v)
Π {A = A} B = (x : A) → B x

pi-syntax : ∀ {u v} (A : Type u) (B : A → Type v) → Type (u ⊔ v)
pi-syntax A = Π {A = A}
syntax pi-syntax A (λ x → M) = Π x ∶ A , M
{-# DISPLAY pi-syntax A B = Π {A = A} B #-}

-- Wild natural transformations
Nt : ∀ {u v w} {X : Type u} → (X → Type v) → (X → Type w) → Type (u ⊔ v ⊔ w)
Nt A B = ∀ x → A x → B x

flip : ∀ {u v w} {A : Type u} {B : Type v} {C : Type w}
     → (A → B → C) → (B → A → C)
flip f = λ x y → f y x
{-# INLINE flip #-}

flipd : ∀ {u v w : Level} {A : Type u} {B : Type v} {C : A → B → Type w}
      → (∀ a b → C a b) → (∀ b a → C a b)
flipd f b a = f a b
{-# INLINE flipd #-}

-- S-combinator
_∘s_ : ∀ {u v w} {A : Type u} {B : A → Type v} {C : (x : A) → B x → Type w}
    → ({x : A} (y : B x) → C x y) → (f : (x : A) → B x) (x : A) → C x (f x)
g ∘s f = λ x → g (f x)
{-# INLINE _∘s_ #-}

-- _∘_ : ∀ {u v w} {A : Type u} {B : Type v} {C : B → Type w}
--      → ((y : B) → C y) → (f : A → B) (x : A) → C (f x)
-- _∘_ g f = λ x → g (f x)
-- {-# INLINE _∘_ #-}

_$_ : ∀ {u v} {A : Type u} {B : A → Type v}
    → (f : (a : A) → B a) (x : A) → B x
f $ a = f a
{-# INLINE _$_ #-}

_&_ : ∀ {u v} {A : Type u} {B : A → Type v}
    → (x : A) (f : (a : A) → B a) → B x
a & f = f a
{-# INLINE _&_ #-}

auto : ∀ {ℓ} {A : Type ℓ} → ⦃ A ⦄ → A
auto ⦃ (a) ⦄ = a

autoω : {A : Typeω} → ⦃ A ⦄ → A
autoω ⦃ (a) ⦄ = a

-- Explicit type hint
the : ∀ {ℓ} (A : Type ℓ) → A → A
the _ a = a

instance
  Cut-funcomp : ∀ {u v w} {A : Type u} {B : Type v} {C : B → Type w}
              → Cut (∀ y → C y) (λ _ → A → B) (λ _ f → (x : A) → C (f x))
  Cut-funcomp .Cut.seq {x = g} f x = g (f x)

```agda

{-# OPTIONS --safe --cubical-compatible #-}

module Data.Pi where

open import Prim.Type
open import Meta.Cut public
open import Meta.Underlying public

-- This is the one Control module we'll allow in Prim due to how fundamental
-- function composition is, and we want it as soon as possible

infixr -1 _$_ _&_
infix 2 _~>_ _~~>_

infix -1 Π-syntax

Π : ∀ {u v} {A : Type u} (B : A → Type v) → Type (u ⊔ v)
Π {A = A} B = (x : A) → B x

Π-syntax : ∀ {u v} (A : Type u) (B : A → Type v) → Type (u ⊔ v)
Π-syntax A = Π {A = A}
syntax Π-syntax A (λ x → M) = Π x ∶ A , M
{-# DISPLAY Π-syntax A B = Π {A = A} B #-}

-- Wild natural transformations
_~>_ : ∀ {u v w} {X : Type u} → (X → Type v) → (X → Type w) → Type (u ⊔ v ⊔ w)
_~>_ A B = ∀ x → A x → B x

-- From Idris: type of natural transformations "with explicit 0-morphisms"
_~~>_ : ∀ {u v w} {X : Type u} → (X → Type v) → (X → Type w) → X → Type (v ⊔ w)
_~~>_ A B x = A x → B x
{-# DISPLAY _~~>_ P Q _ = P ~> Q #-}

flip : ∀ {u v w} {A : Type u} {B : Type v} {C : Type w}
     → (A → B → C) → (B → A → C)
flip f = λ x y → f y x
{-# INLINE flip #-}

bflip : ∀ {u v w} {A : Type u} {B : Type v} {C : A → B → Type w}
     → (∀ a b → C a b) → (∀ b a → C a b)
bflip f b a = f a b
{-# INLINE bflip #-}

_on_ : ∀ {u v w} {A : Type u} {B : Type v} {C : B → B → Type w}
     → ((x y : B) → C x y)
     → (f : A → B)
     → (x y : A) → C (f x) (f y)
(_∎_ on f) x y = f x ∎ f y

-- S-combinator
_∘s_ : ∀ {u v w} {A : Type u} {B : A → Type v} {C : (x : A) → B x → Type w}
    → ({x : A} (y : B x) → C x y) → (f : (x : A) → B x) (x : A) → C x (f x)
g ∘s f = λ x → g (f x)
{-# INLINE _∘s_ #-}

_$_ : ∀ {u v} {A : Type u} {B : A → Type v}
    → (f : (a : A) → B a) (x : A) → B x
_$_ = id
{-# INLINE _$_ #-}

_&_ : ∀ {u v} {A : Type u} {B : A → Type v}
    → (x : A) (f : (a : A) → B a) → B x
a & f = f a
{-# INLINE _&_ #-}

it : ∀ {ℓ} {A : Type ℓ} → ⦃ A ⦄ → A
it ⦃ (a) ⦄ = a

itω : {A : Typeω} → ⦃ A ⦄ → A
itω ⦃ (a) ⦄ = a

-- Explicit type hint
the : ∀ {ℓ} (A : Type ℓ) → A → A
the _ a = a

outl : ∀ {u v} {A : Type u} {B : A → Type v} → ∀ a → B a → A
outl a = const a

outr : ∀ {u v} {A : Type u} {B : A → Type v} → ∀ a → B a → B a
outr a = id

instance
  Cut-funcomp : ∀ {u v w} {B : Type v} {C : B → Type w}
              → Cut (λ (A : Type u) → A → B)
                    (λ _ → Π C)
                    (λ A f → (x : A) → C (f x))
  Cut-funcomp .Cut.seq {x = A} f g x = g (f x)

  -- Cut-S-combinator : ∀ {u v w} {A : Type v} {B : A → Type v} {C : (x : A) → B x → Type w}
  --             → Cut (λ U → {!T!})
  --                   (λ x → {!!})
  --                   (λ A f → (x : A) → {!!})
  -- Cut-S-combinator .Cut.seq {x = A} f g x = g (f x)

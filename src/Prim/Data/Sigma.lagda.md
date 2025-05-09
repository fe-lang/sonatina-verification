```agda

{-# OPTIONS --safe --cubical-compatible #-}

module Prim.Data.Sigma where

open import Prim.Type using (Type; _⊔_ )

infixr 5 _×_
infixr -1 Σ-syntax 

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

Σ-syntax = Sigma
syntax Σ-syntax A (λ x → M) = Σ x ∶ A , M
{-# DISPLAY Σ-syntax _ B = Σ B #-}
{-# DISPLAY Sigma A B = Σ B #-}
```

Next we define our induction principle for the Sigma type, which is
uncurrying, while the evaluation map of the Sigma type is currying.

```
module _ {u v w} {A : Type u} {B : A → Type v} (P : Σ B → Type w) where
  Σ-ind : ((x : A) (y : B x) → P (x , y)) → (z : Σ B) → P z
  Σ-ind g z = g (fst z) (snd z)

  -- indβ-Σ : (g : (x : A) (y : B x) → P (x , y)) ((x , y) : Σ B)
  --      → ind-Σ g (x , y) ＝ g x y
  -- indβ-Σ g z i = g (fst z) (snd z)

  Σ-ev : ((z : Σ B) → P z) → (x : A) (y : B x) → P (x , y)
  Σ-ev g x y = g (x , y)

```

We also present our native notion of Cartesian product, with its
corresponding induction rule.

```
_×_ : ∀ {ℓ ℓ'} → Type ℓ → Type ℓ' → Type (ℓ ⊔ ℓ')
A × B = Sigma A (λ _ → B)

diag : ∀ {ℓ} {A : Type ℓ} → A → A × A
diag a = a , a

swap : ∀ {u v} {A : Type u} {B : Type v} → A × B → B × A
swap (a , b) = b , a

ind-× : ∀ {u v w} {A : Type u} {B : Type v} (P : A × B → Type w)
      → ((x : A) (y : B) → P (x , y)) → (z : A × B) → P z
ind-× P g z = g (fst z) (snd z)



  -- indβ-× : ∀ {u v w} {A : Type u} {B : Type v} (P : A × B → Type w)
  --        → (g : (x : A) (y : B) → P (x , y)) ((x , y) : A × B)
  --        → ind-× g (x , y) ＝ g x y
  -- indβ-× g z i = g (fst z) (snd z)

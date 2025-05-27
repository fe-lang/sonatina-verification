```agda

{-# OPTIONS --safe --erased-cubical #-}

module Data.Sigma.Base where

open import Prim.Type
open import Trait.Contr
open import Data.Path.Type

open import Data.Sigma.Type public

```

Here we define our induction principle for the Sigma type, which is
uncurrying, while the evaluation map of the Sigma type is currying.

```
module _ {u v w} {A : Type u} {B : A → Type v} (P : Σ B → Type w) where
  Σ-ind : ((x : A) (y : B x) → P (x , y)) → (z : Σ B) → P z
  Σ-ind g z = g (fst z) (snd z)

  Σ-indβ : (g : (x : A) (y : B x) → P (x , y)) ((x , y) : Σ B)
         → Σ-ind g (x , y) ＝ g x y
  Σ-indβ g z i = g (fst z) (snd z)

  Σ-ev : ((z : Σ B) → P z) → (x : A) (y : B x) → P (x , y)
  Σ-ev g x y = g (x , y)

Σ-map : ∀ {u v w} {A : Type u} {P : A → Type v} {Q : A → Type w}
      → (∀ x → P x → Q x) → Σ P → Σ Q
Σ-map {Q} η = Σ-ind (λ _ → Σ Q) λ x p → x , η x p

```

We also present our native notion of Cartesian product, with its
corresponding induction rule.

```

diag : ∀ {ℓ} {A : Type ℓ} → A → A × A
diag a = a , a

swap : ∀ {u v} {A : Type u} {B : Type v} → A × B → B × A
swap (a , b) = b , a

×-ind : ∀ {u v w} {A : Type u} {B : Type v} (P : A × B → Type w)
    → ((x : A) (y : B) → P (x , y)) → (z : A × B) → P z
×-ind P g z = g (fst z) (snd z)

×-indβ : ∀ {u v w} {A : Type u} {B : Type v} (P : A × B → Type w)
       → (g : (x : A) (y : B) → P (x , y)) ((x , y) : A × B)
       → ×-ind P g (x , y) ＝ g x y
×-indβ P g z i = g (fst z) (snd z)

×-map : ∀ {u v w z} {A : Type u} {B : Type v} {C : Type w} {D : Type z}
      → (A → C) → (B → D) → A × B → C × D
×-map {C} {D} f g = ×-ind (λ _ → C × D) λ x y → f x , g y

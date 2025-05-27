```agda
{-# OPTIONS --safe --erased-cubical #-}

module Trait.Inverse where

open import Prim.Type renaming (funcomp to infixr 40 _∘_)
open import Prim.Interval
open import Data.Path.Transport
open import Data.Path.Reasoning
open import Data.Path.Base
open import Data.Sigma.Type

```

The type of Quasi-inverses (simply called "Isomorphisms" in many iterations of HoTT)

```

record has-inverse {u v} {A : Type u} {B : Type v} (f : A → B) : Type (u ⊔ v) where
  field
    inv : B → A
    sec : (x : A) → inv (f x) ＝ x
    retr : (y : B) → f (inv y) ＝ y

  fun = f

open has-inverse public
  renaming ( fun to inverse-fun
           ; inv to inverse-inv
           ; sec to inverse-sec
           ; retr to inverse-retr)

Iso : ∀ {u v} → Type u → Type v → Type (u ⊔ v)
Iso A B = Sigma (A → B) has-inverse

isotofun : ∀ {u v} {A : Type u} {B : Type v} → Iso A B → A → B
isotofun = fst

module Iso {u v} {A : Type u} {B : Type v} (e : Iso A B) where
  fun : A → B
  fun = fst e

  inv : B → A
  inv = e .snd .inverse-inv

  sec : (x : A) → inv (fun x) ＝ x
  sec = e .snd .inverse-sec

  retr : (y : B) → fun (inv y) ＝ y
  retr = e .snd .inverse-retr

Iso-refl : ∀ {u} (A : Type u) → Iso A A
Iso-refl A .fst = id
Iso-refl A .snd .inverse-inv = id
Iso-refl A .snd .inverse-sec = erefl
Iso-refl A .snd .inverse-retr = erefl

Iso-inv : ∀ {u v} {A : Type u} {B : Type v} → Iso A B → Iso B A
Iso-inv (f , e) .fst = inverse-inv e
Iso-inv (f , e) .snd .inverse-inv = f
Iso-inv (f , e) .snd .inverse-sec = e .inverse-retr
Iso-inv (f , e) .snd .inverse-retr = e .inverse-sec

Iso-comp : ∀ {u v w} {A : Type u} {B : Type v} {C : Type w}
          → Iso A B → Iso B C → Iso A C
Iso-comp f g .fst = fst g ∘ fst f 
Iso-comp f g .snd = γ
  where
  module f = Iso f
  module g = Iso g
  fun = g.fun ∘ f.fun
  inv = f.inv ∘ g.inv

  γ : has-inverse fun
  γ .inverse-inv = inv
  γ .inverse-sec x =
    inv (fun x)     ＝⟨ ap f.inv (g.sec (f.fun x)) ⟩
    f.inv (f.fun x) ＝⟨ f.sec x ∣
    x ∎
  γ .inverse-retr y =
    fun (inv y)     ＝⟨ ap g.fun (f.retr (g.inv y)) ⟩
    g.fun (g.inv y) ＝⟨ g.retr y ∣
    y ∎

Σ-PathP-Iso : ∀ {u v} {A : I → Type u} {B : (i : I) → A i → Type v}
    {x : Σ (B i0)} {y : Σ (B i1)}
  → Iso
      (Σ p ∶ PathP A (x .fst) (y .fst) ,
        (PathP (λ i → B i (p i)) (x .snd) (y .snd)))
      (PathP (λ i → Σ (B i)) x y)
Σ-PathP-Iso .fst (p , q) i = p i , q i
Σ-PathP-Iso .snd .inverse-inv p = (λ i → p i .fst) , λ i → p i .snd
Σ-PathP-Iso .snd .inverse-sec p = refl
Σ-PathP-Iso .snd .inverse-retr p = refl

Σ-Path-Iso : ∀ {u v} {A : Type u} {B : A → Type v} {x y : Σ B}
            → Iso (Σ p ∶ x .fst ＝ y .fst , (subst B p (x .snd) ＝ y .snd)) (x ＝ y)
Σ-Path-Iso {B} {x} {y} =
  transport (λ i → Iso (Σ p ∶ x .fst ＝ y .fst
                 , Path-over＝PathP (λ i → B (p i)) (x .snd) (y .snd) (~ i)) (x ＝ y))
            Σ-PathP-Iso

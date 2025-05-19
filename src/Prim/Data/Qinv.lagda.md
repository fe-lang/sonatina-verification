```agda
{-# OPTIONS --safe --erased-cubical #-}

module Prim.Data.Qinv where

open import Prim.Type renaming (funcomp to infixr 40 _∘_)
open import Prim.Interval.Core
open import Prim.Interval.Transport
open import Prim.Reasoning
open import Prim.Data.Path
open import Prim.Data.Sigma

```

The type of Quasi-inverses (simply called "Isomorphisms" in many iterations of HoTT)

```

record has-qinv {u v} {A : Type u} {B : Type v} (f : A → B) : Type (u ⊔ v) where
  field
    inv : B → A
    sec : (x : A) → inv (f x) ＝ x
    retr : (y : B) → f (inv y) ＝ y

  fun = f

open has-qinv public
  renaming ( fun to qinv-fun
           ; inv to qinv-inv
           ; sec to qinv-sec
           ; retr to qinv-retr)

Qinv : ∀ {u v} → Type u → Type v → Type (u ⊔ v)
Qinv A B = Sigma (A → B) has-qinv

qinvtofun : ∀ {u v} {A : Type u} {B : Type v} → Qinv A B → A → B
qinvtofun = fst

module Qinv {u v} {A : Type u} {B : Type v} (e : Qinv A B) where
  fun : A → B
  fun = fst e

  inv : B → A
  inv = e .snd .qinv-inv

  sec : (x : A) → inv (fun x) ＝ x
  sec = e .snd .qinv-sec

  retr : (y : B) → fun (inv y) ＝ y
  retr = e .snd .qinv-retr

Qinv-refl : ∀ {u} (A : Type u) → Qinv A A
Qinv-refl A .fst = id
Qinv-refl A .snd .qinv-inv = id
Qinv-refl A .snd .qinv-sec = erefl
Qinv-refl A .snd .qinv-retr = erefl

Qinv-inv : ∀ {u v} {A : Type u} {B : Type v} → Qinv A B → Qinv B A
Qinv-inv (f , e) .fst = qinv-inv e
Qinv-inv (f , e) .snd .qinv-inv = f
Qinv-inv (f , e) .snd .qinv-sec = e .qinv-retr
Qinv-inv (f , e) .snd .qinv-retr = e .qinv-sec

Qinv-comp : ∀ {u v w} {A : Type u} {B : Type v} {C : Type w}
          → Qinv A B → Qinv B C → Qinv A C
Qinv-comp f g .fst = fst g ∘ fst f 
Qinv-comp f g .snd = γ
  where
  module f = Qinv f
  module g = Qinv g
  fun = g.fun ∘ f.fun
  inv = f.inv ∘ g.inv

  γ : has-qinv fun
  γ .qinv-inv = inv
  γ .qinv-sec x =
    inv (fun x)     ＝⟨ ap f.inv (g.sec (f.fun x)) ⟩
    f.inv (f.fun x) ＝⟨ f.sec x ∣
    x ∎
  γ .qinv-retr y =
    fun (inv y)     ＝⟨ ap g.fun (f.retr (g.inv y)) ⟩
    g.fun (g.inv y) ＝⟨ g.retr y ∣
    y ∎

Σ-PathP-Qinv : ∀ {u v} {A : I → Type u} {B : (i : I) → A i → Type v}
    {x : Σ (B i0)} {y : Σ (B i1)}
  → Qinv
      (Σ p ∶ PathP A (x .fst) (y .fst) ,
        (PathP (λ i → B i (p i)) (x .snd) (y .snd)))
      (PathP (λ i → Σ (B i)) x y)
Σ-PathP-Qinv .fst (p , q) i = p i , q i
Σ-PathP-Qinv .snd .qinv-inv p = (λ i → p i .fst) , λ i → p i .snd
Σ-PathP-Qinv .snd .qinv-sec p = refl
Σ-PathP-Qinv .snd .qinv-retr p = refl

Σ-Path-Qinv : ∀ {u v} {A : Type u} {B : A → Type v} {x y : Σ B}
            → Qinv (Σ p ∶ x .fst ＝ y .fst , (subst B p (x .snd) ＝ y .snd)) (x ＝ y)
Σ-Path-Qinv {B} {x} {y} =
  transport (λ i → Qinv (Σ p ∶ x .fst ＝ y .fst
                 , Path＝PathP (λ i → B (p i)) (x .snd) (y .snd) (~ i)) (x ＝ y))
            Σ-PathP-Qinv

```agda

{-# OPTIONS --safe --erased-cubical #-}

module Prim.Equiv where

open import Prim.Type using (Level; Type; _⊔_) renaming (funcomp to infixr 40 _∘_) using ()
open import Prim.Pi
open import Prim.Interval.Core
open import Prim.Interval.Transport using (coe; transport; transport-refl; module coe; is-contr→extend)
open import Prim.Interval.Kan using (hcomp; _∙∙_∙∙_ ; path-filler)
open import Prim.Interval.Fill
  using (neutral-square; module tri; path-cfiller)
open import Prim.Fiber

open import Prim.Data.Path
open import Prim.Data.Sigma
open import Prim.Data.Contr
open import Prim.Data.Qinv

record is-equiv {u v} {A : Type u} {B : Type v} (f : A → B) : Type (u ⊔ v) where
  no-eta-equality
  constructor equiv
  field
    inv : B → A
    sec : (x : A) → inv (f x) ＝ x
    retr : (y : B) → f (inv y) ＝ y
    adj : (x : A) → ap f (sec x) ＝ retr (f x)

  fun = f

  inv-adj : ∀ y → ap inv (retr y) ＝ sec (inv y)
  inv-adj y =
    let
      pf : (x : A) → ap inv (retr (f x)) ＝ sec (inv (f x))
      pf x i j = hcomp (∂ i ∨ ∂ j) λ where
        k (i = i0) → inv (retr (f x) (j ∨ ~ k))
        k (i = i1) → sec (sec x (~ k)) j
        k (j = i0) → inv (adj x (~ i) (~ k))
        k (j = i1) → sec x (i ∧ ~ k)
        k (k = i0) → sec x (i ∧ j)
    in
      transp (λ i → ap inv (retr (retr y i)) ＝ sec (inv (retr y i)))
        i0 (pf (inv y))

open is-equiv public
  renaming ( fun to eqv-fun
           ; inv to eqv-inv
           ; sec to eqv-sec
           ; retr to eqv-retr
           ; adj to eqv-adj
           ; inv-adj to eqv-inv-adj )


_≃_ : ∀ {u v} → Type u → Type v → Type (u ⊔ v)
A ≃ B = Σ {A = A → B} is-equiv
{-# BUILTIN EQUIV      _≃_   #-}

eqvtofun : ∀ {u v} {A : Type u} {B : Type v} → A ≃ B → A → B
eqvtofun e = fst e
{-# BUILTIN EQUIVFUN   eqvtofun  #-}

module _ {u v} {A : Type u} {B : Type v} {f : A → B} (e : has-qinv f) where
  private
    module e = qinv→contr-fibers e

  qinv→equiv : is-equiv f
  qinv→equiv .is-equiv.inv = e .qinv-inv
  qinv→equiv .is-equiv.sec x = e.unit (x , refl)
  qinv→equiv .is-equiv.retr = e .qinv-retr
  qinv→equiv .is-equiv.adj x = e.adj (x , refl)

equiv→qinv : ∀ {u v} {A : Type u} {B : Type v} {f : A → B}
           → is-equiv f → has-qinv f
equiv→qinv e .qinv-inv = e .eqv-inv
equiv→qinv e .qinv-sec = e .eqv-sec
equiv→qinv e .qinv-retr = e .eqv-retr

Qinv→Equiv : ∀ {u v} {A : Type u} {B : Type v} (e : Qinv A B) → A ≃ B
Qinv→Equiv e = e .fst , qinv→equiv (e .snd)

Equiv→Qinv : ∀ {u v} {A : Type u} {B : Type v} → A ≃ B → Qinv A B
Equiv→Qinv e = e .fst , equiv→qinv (e .snd)

transport-is-equiv : ∀ {ℓ} (A : I → Type ℓ) → is-equiv (coe A i1)
transport-is-equiv A .eqv-inv = coe (λ i → A (~ i)) i1
transport-is-equiv A .eqv-sec = transport.unit A
transport-is-equiv A .eqv-retr = transport.counit A
transport-is-equiv A .eqv-adj = transport.adj A

id-is-equiv : ∀ {u} {A : Type u} → is-equiv {A = A} (λ x → x)
id-is-equiv .eqv-inv = λ x → x
id-is-equiv .eqv-sec = erefl
id-is-equiv .eqv-retr = erefl
id-is-equiv .eqv-adj x = refl

pathtoeqv : ∀ {u} {A B : Type u} → A ＝ B → A ≃ B
pathtoeqv P = transport P , transport-is-equiv λ i → P i

module Equiv {u v} {A : Type u} {B : Type v} ((f , e) : A ≃ B) where
  private
    module e = is-equiv e
  inv = e.inv
  η = e.sec
  ε = e.retr
  α = e.adj

  inverse : B ≃ A
  inverse .fst = inv
  inverse .snd .eqv-inv = f
  inverse .snd .eqv-sec = ε
  inverse .snd .eqv-retr = η
  inverse .snd .eqv-adj = e.inv-adj

  private
    g = inv
    module _ {y : B} ((x , p) : fiber f y) where
      path : g y ＝ x
      path = ap g (sym p) ∙∙ refl ∙∙ η x

      filler : ε y ⌞ ap f path ⌟ p ⇒ refl
      filler i j = hcomp (∂ i ∨ ∂ j) λ where
        k (i = i0) → ε (p k) j
        k (i = i1) → neutral-square (ap f (η x)) p j k
        k (j = i0) → f (path-filler (ap g p) refl (η x) i k)
        k (j = i1) → p k
        k (k = i0) → α x (~ i) j

  prop : {y : B} (z : fiber f y) → Path (fiber f y) (g y , ε y) z
  prop z i .fst = path z i
  prop z i .snd = filler z i

  contr : (y : B) → is-contr (fiber f y)
  contr y .ctr = g y , ε y
  contr y .paths = prop

  fequiv : is-fequiv f
  fequiv .is-fequiv.is-feqv = contr

open Equiv public
  renaming ( contr to Equiv→contr-fibers
           ; fequiv to Equiv→fequiv )
  using ()

equiv-proof : ∀ {u v} (T : Type u) (A : Type v) (w : T ≃ A) (a : A)
            → ∀ φ (u : Partial φ (fiber (w .fst) a)) → fiber (w .fst) a [ φ ↦ u ]
equiv-proof {u} {v} T A w a = is-contr→extend (Equiv→contr-fibers w a)

{-# BUILTIN EQUIVPROOF equiv-proof #-}

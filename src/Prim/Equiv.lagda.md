```agda

{-# OPTIONS --safe --erased-cubical #-}

module Prim.Equiv where

open import Prim.Type using (Type; _⊔_)
open import Prim.Cubical
open import Prim.Kan
  using (hcomp; hfill)
  renaming (path-comp to _∙_)
open import Prim.Fill
  using (hcomp-fill; neutral-square; sq-rwhisker; sq-lswap)

open import Prim.Data.Path
open import Prim.Data.Sigma
open import Prim.Data.Contr

record is-equiv {u v} {A : Type u} {B : Type v} (f : A → B) : Type (u ⊔ v) where
  no-eta-equality
  constructor equiv
  field
    inv : B → A
    sec : (x : A) → inv (f x) ＝ x
    retr : (y : B) → f (inv y) ＝ y
    adj : (x : A) → ap f (sec x) ＝ retr (f x)

  fun = f

  abstract
    inv-adj : ∀ y → ap inv (retr y) ＝ sec (inv y)
    inv-adj b =
      let
        pf : (x : A) → ap inv (retr (f x)) ＝ sec (inv (f x))
        pf x i j = hcomp (∂ i ∨ ∂ j) λ where
          k (i = i0) → inv (retr (f x) (j ∨ ~ k))
          k (i = i1) → sec (sec x (~ k)) j
          k (j = i0) → inv (adj x (~ i) (~ k))
          k (j = i1) → sec x (i ∧ ~ k)
          k (k = i0) → sec x (i ∧ j)
      in
        transp (λ i → ap inv (retr (retr b i)) ＝ sec (inv (retr b i)))
          i0 (pf (inv b))

open is-equiv public
  renaming ( fun to eqv-fun
           ; inv to eqv-inv
           ; sec to eqv-sec
           ; retr to eqv-retr
           ; adj to eqv-adj
           ; inv-adj to eqv-inv-adj )

_≃_ : ∀ {u v} → Type u → Type v → Type (u ⊔ v)
A ≃ B = Σ f ∶ (A → B) , is-equiv f
{-# BUILTIN EQUIV      _≃_   #-}

eqtofun : ∀ {u v} {A : Type u} {B : Type v} → A ≃ B → A → B
eqtofun e = fst e
{-# BUILTIN EQUIVFUN   eqtofun   #-}

module equiv-fibers {u v} {A : Type u} {B : Type v}
  (f : A → B) (g : B → A)
  (η : (x : A) → g (f x) ＝ x)
  (ε : (y : B) → f (g y) ＝ y)
  (α : (x : A) → ap f (η x) ＝ ε (f x))
  {y : B} (z : fiber f y)
  where
  open Σ z renaming (fst to x; snd to p)

  path : g y ＝ x
  path = ap g (sym p) ∙ η x

  private
    σ : refl  ⌞ ap f path ⌟ p ⇒ ε y
    σ i j = hcomp (∂ i ∨ ∂ j) λ where
      k (i = i0) → f (g (p (~ j ∨ k)))
      k (i = i1) → sq-rwhisker (ap f (η x)) (ε (f x)) p (α x) j k
      k (j = i0) → f (hcomp-fill refl (ap g (sym p)) (η x) i k)
      k (j = i1) → ε (p k) i
      k (k = i0) → neutral-square (ap f (ap g (sym p))) (ε (f x)) i j

  filler : ε y ⌞ ap f path ⌟ p ⇒ refl
  filler = sq-lswap (ap f path) p (ε y) σ

  contr : Path (fiber f y) (g y , ε y) (x , p)
  contr i .fst = path i
  contr i .snd = filler i

equiv-fibers : ∀ {u v} (A : Type u) (B : Type v) (w : A ≃ B) {y : B}
            → (let f = w .fst)
            → is-contr (fiber f y)
equiv-fibers A B w {(y)} .ctr = w .snd .eqv-inv y , w .snd .eqv-retr y
equiv-fibers A B w .paths z = equiv-fibers.contr e.fun e.inv e.sec e.retr e.adj z
  where module e = is-equiv (w .snd)

equiv-proof : ∀ {u v} (T : Type u) (A : Type v) → (w : T ≃ A) → (a : A)
            → ∀ ψ (f : Partial ψ (fiber (w .fst) a)) → fiber (w .fst) a [ ψ ↦ f ]
equiv-proof A B w a ψ fb =
  inS (contr' {A = fiber (w .fst) a} (equiv-fibers A B w) ψ fb)
  where
    contr' : ∀ {ℓ} {A : Type ℓ} → is-contr A → (φ : I) → (u : Partial φ A) → A
    contr' (c , p) φ u = hcomp (∂ φ) λ where
      i (φ = i1) → p (u 1=1) i
      i (φ = i0) → c
      i (i = i0) → c

{-# BUILTIN EQUIVPROOF equiv-proof #-}

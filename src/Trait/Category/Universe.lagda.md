```agda
{-# OPTIONS --safe --erased-cubical #-}

module Trait.Category.Universe where

open import Prim.Type
open import Prim.Equiv
open import Prim.Data.Path
open import Prim.Data.Qinv
open import Prim.Fill using (path-idnl; path-idnr; path-idpt; path-assoc)
open import Prim.Fiber
open import Prim.Data.Sigma
open import Meta.Cut

open import Trait.Category.Type
open import Data.Category

private
  post : ∀ {ℓ} {A : Type ℓ} {x y : A} → x ＝ y → x ＝ y
  post {x = x} {y} = λ (p : x ＝ y) → p ∙ refl

  pre : ∀ {ℓ} {A : Type ℓ} {x y : A} → x ＝ y → x ＝ y
  pre {x = x} {y} = λ (p : x ＝ y) → refl ∙ p

module _ {ℓ} {A : Type ℓ} {x y : A} where
  private
    η : (p : x ＝ y) → refl ∙ (p ∙ refl) ＝ p
    η p = path-idnl (p ∙ refl) ∙ path-idnr p

    ε : (p : x ＝ y) → (refl ∙ p) ∙ refl ＝ p
    ε p = path-idnr (refl ∙ p) ∙ path-idnl p

    q-post : Qinv (x ＝ y) (x ＝ y)
    q-post .fst = post
    q-post .snd .qinv-inv = pre
    q-post .snd .qinv-sec = η
    q-post .snd .qinv-retr = ε

    q-pre : Qinv (x ＝ y) (x ＝ y)
    q-pre .fst = pre
    q-pre .snd .qinv-inv = post
    q-pre .snd .qinv-sec = ε
    q-pre .snd .qinv-retr = η

    -- TODO: A direct proof is preferable, but this will do for now
    module post (p : x ＝ y) = qinv→contr-fibers q-post
    module pre (p : x ＝ y) = qinv→contr-fibers q-pre

  refl-post-equiv : is-equiv post
  refl-post-equiv = qinv→equiv q-post

  refl-pre-equiv : is-equiv pre
  refl-pre-equiv = qinv→equiv q-pre

typ-is-category : ∀ {ℓ} (A : Type ℓ) → is-category (Path A) _∙_
typ-is-category A x .has-identity.idn = refl
typ-is-category A x .has-identity.idn-idpt = path-idpt x
typ-is-category A x .has-identity.idn-sec y = refl-pre-equiv
typ-is-category A x .has-identity.idn-retr y = refl-post-equiv

∞-Grpd : ∀ {ℓ} (A : Type ℓ) → Category ℓ ℓ
∞-Grpd A .Category.Ob = A
∞-Grpd A .Category.Hom = _＝_
∞-Grpd A .Category.seq = _∙_
∞-Grpd A .Category.assoc = path-assoc
∞-Grpd A .Category.is-cat = typ-is-category A

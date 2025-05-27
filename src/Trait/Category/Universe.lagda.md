```agda
{-# OPTIONS --safe --erased-cubical #-}

module Trait.Category.Universe where

open import Prim.Type
open import Trait.Equiv
open import Data.Path.Type
open import Trait.Inverse
open import Data.Path.Square using (path-idnl; path-idnr; path-idpt; path-assoc)
open import Lib.Fiber
open import Data.Sigma.Type
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

    q-post : Iso (x ＝ y) (x ＝ y)
    q-post .fst = post
    q-post .snd .inverse-inv = pre
    q-post .snd .inverse-sec = η
    q-post .snd .inverse-retr = ε

    q-pre : Iso (x ＝ y) (x ＝ y)
    q-pre .fst = pre
    q-pre .snd .inverse-inv = post
    q-pre .snd .inverse-sec = ε
    q-pre .snd .inverse-retr = η

  refl-post-equiv : is-equiv post
  refl-post-equiv = inverse→equiv (q-post .snd)

  refl-pre-equiv : is-equiv pre
  refl-pre-equiv = inverse→equiv (q-pre .snd)

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

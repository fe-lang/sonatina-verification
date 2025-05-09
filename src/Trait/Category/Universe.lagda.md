```agda
{-# OPTIONS --safe --erased-cubical #-}

module Trait.Category.Universe where

open import Prim.Type
open import Prim.Equiv using ( is-equiv; eqv-inv; eqv-sec; eqv-retr; eqv-adj )
open import Prim.Data.Path
open import Prim.Kan renaming ( path-comp to _∙_ )
open import Prim.Fill using ( path-idnl; path-idnr; path-idpt; path-assoc )
open import Prim.Fiber using ( module contr-fibers )
open import Prim.Data.Sigma

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

    -- TODO: A direct proof is preferable, but this will do for now
    module post (p : x ＝ y) = contr-fibers post pre η ε (p , refl)
    module pre (p : x ＝ y) = contr-fibers pre post ε η (p , refl)

  refl-post-equiv : is-equiv post
  refl-post-equiv .eqv-inv = pre
  refl-post-equiv .eqv-sec = post.unit
  refl-post-equiv .eqv-retr = ε
  refl-post-equiv .eqv-adj = post.zig

  refl-pre-equiv : is-equiv pre
  refl-pre-equiv .eqv-inv = post
  refl-pre-equiv .eqv-sec = pre.unit
  refl-pre-equiv .eqv-retr = η
  refl-pre-equiv .eqv-adj = pre.zig

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

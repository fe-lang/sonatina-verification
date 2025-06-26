```agda
{-# OPTIONS --safe --erased-cubical #-}

module Trait.Algebra.Separation where

open import Lib.Base
open import Meta.Idiom

open import Trait.Category

Own : ∀ {u} {Res : Type u} → Res → Res → Type u
Own a = λ b → b ＝ a

record has-separation-algebra {u v} {Res : Type u}
  (_*_≃_ : Res → Res → Res → Type v)
  : Type (u ⊔ v)
  where
  field
    unit : Res
    eq-idnl : ∀ {a} → unit * a ≃ a
    eq→path : ∀ {a b} → unit * a ≃ b → a ＝ b
    eq-comm : ∀ {a b c} → a * b ≃ c → b * a ≃ c
    eq-assoc : ∀ {a b c ab abc}
             → a * b ≃ ab → ab * c ≃ abc
             → Σ bc ∶ Res , a * bc ≃ abc × b * c ≃ bc

Separation-alg : ∀ u v → Type₊ (u ⊔ v)
Separation-alg u v = Σ Res ∶ Type u
                   , Σ Eq ∶ (Res → Res → Res → Type v)
                   , has-separation-algebra Eq

module Separation-alg {u v} ((R , E , Alg) : Separation-alg u v) where
  open has-separation-algebra Alg public

  Res : Type u
  Res = R

  _*_≃_ : Res → Res → Res → Type v
  _*_≃_ = E

  Pred : ∀ w → Type (u ⊔ w ₊)
  Pred w = Res → Type w

  Emp : Pred u
  Emp = Own unit

  Own-is-contr : (x : Res) → is-contr (Σ (Own x))
  Own-is-contr x .ctr = x , refl
  Own-is-contr x .paths (y , p) i = p (~ i) , λ j → p (~ i ∨ j)

  Emp-is-contr : is-contr (Σ Emp)
  Emp-is-contr = Own-is-contr unit

  infix 2 emp-syntax
  emp-syntax : Pred u → Type u
  emp-syntax P = P unit

  syntax emp-syntax P = ε∎ P

module _ {o e} ⦃ S : Separation-alg o e ⦄ where
  open Separation-alg S
  private ℓ = o ⊔ e

  infixr 10 _✴_

```

Separating Conjunction definition and laws

```
  record _✴_ {u v} (P : Pred u) (Q : Pred v) (a : Res) : Type (ℓ ⊔ u ⊔ v) where
    constructor _∙⟨_⟩_
    field
      {al ar} : Res
      px : P al
      sep : al * ar ≃ a
      qx : Q ar

  sconj-swap : ∀ {u v} {P : Pred u} {Q : Pred v} → ∀∎ P ✴ Q ~~> Q ✴ P
  sconj-swap (px ∙⟨ sep ⟩ qx) ._✴_.al = _
  sconj-swap (px ∙⟨ sep ⟩ qx) ._✴_.ar = _
  sconj-swap (px ∙⟨ sep ⟩ qx) ._✴_.px = qx
  sconj-swap (px ∙⟨ sep ⟩ qx) ._✴_.sep = eq-comm sep
  sconj-swap (px ∙⟨ sep ⟩ qx) ._✴_.qx = px

  sconj-assocr : ∀ {u v w} {P : Pred u} {Q : Pred v} {R : Pred w}
              → ∀∎ (P ✴ Q) ✴ R ~~> P ✴ (Q ✴ R)
  sconj-assocr ((px ∙⟨ sep₁ ⟩ qx) ∙⟨ sep ⟩ rx) ._✴_.al = _
  sconj-assocr ((px ∙⟨ s ⟩ qx) ∙⟨ r ⟩ rx) ._✴_.ar = eq-assoc s r .fst
  sconj-assocr ((px ∙⟨ sep₁ ⟩ qx) ∙⟨ sep ⟩ rx) ._✴_.px = px
  sconj-assocr ((px ∙⟨ s ⟩ qx) ∙⟨ r ⟩ rx) ._✴_.sep = eq-assoc s r .snd .fst
  sconj-assocr ((px ∙⟨ s ⟩ qx) ∙⟨ r ⟩ rx) ._✴_.qx = qx ∙⟨ eq-assoc s r .snd .snd ⟩ rx

  sconj-rotater : ∀ {u v w} {P : Pred u} {Q : Pred v} {R : Pred w}
                → ∀∎ P ✴ Q ✴ R ~~> R ✴ P ✴ Q
  sconj-rotater (px ∙⟨ p ⟩ (qx ∙⟨ q ⟩ rx)) ._✴_.al = _
  sconj-rotater (px ∙⟨ p ⟩ (qx ∙⟨ q ⟩ rx)) ._✴_.ar =
    eq-assoc (eq-comm q) (eq-comm p) .fst
  sconj-rotater (px ∙⟨ p ⟩ (qx ∙⟨ q ⟩ rx)) ._✴_.px = rx
  sconj-rotater (px ∙⟨ p ⟩ (qx ∙⟨ q ⟩ rx)) ._✴_.sep =
    eq-assoc (eq-comm q) (eq-comm p) .snd .fst
  sconj-rotater (px ∙⟨ p ⟩ (qx ∙⟨ q ⟩ rx)) ._✴_.qx =
    px ∙⟨ eq-comm (eq-assoc (eq-comm q) (eq-comm p) .snd .snd) ⟩ qx

  sconj-idn-to : ∀ {u} {P : Pred u} → ∀∎ P ~~> P ✴ Emp
  sconj-idn-to p ._✴_.al = _
  sconj-idn-to p ._✴_.ar = unit
  sconj-idn-to p ._✴_.px = p
  sconj-idn-to p ._✴_.sep = eq-comm eq-idnl
  sconj-idn-to p ._✴_.qx = eq→path eq-idnl

  sconj-idn-from : ∀ {u} {P : Pred u} → ∀∎ Emp ✴ P ~~> P
  sconj-idn-from {P} (px ∙⟨ sep ⟩ qx) = subst P (eq→path γ) qx where
    γ : unit * _ ≃ _
    γ = subst (_* _ ≃ _) px sep

```

Separating Implication ('Magic Wand') definition

\st5 for ✴

```
  record _-✴_ {u v} (P : Pred u) (Q : Pred v) (a0 : Res) : Type (ℓ ⊔ u ⊔ v) where
    field
      wand : ∀ {a1 a} → a0 * a1 ≃ a → P a1 → Q a

```

Writer Monad

```

  Writer : ∀ {u v w} {J : Type u} → (J → J → Pred v) → J → J → Pred w → Pred (o ⊔ e ⊔ v ⊔ w)
  Writer W j1 j2 P = W j1 j2 ✴ P

  record Indexed-monoid {u} {K : Type u} (W : K → K → Pred o) : Type (u ⊔ o ⊔ e) where
    field
      mempty : {a : K} → ε∎ W a a
      mappend : {l1 l2 l3 : K} → ∀∎ W l1 l2 ~~> W l2 l3 -✴ W l1 l3


```

Kleene Star

```

  data Star {u} (P : Pred u) : Res → Type (o ⊔ e ⊔ u) where
    nil : Star P unit
    cons : ∀∎ P ✴ Star P ~~> Star P

  Plus : ∀ {u} → Pred u → Pred (o ⊔ e ⊔ u)
  Plus P = P ✴ Star P

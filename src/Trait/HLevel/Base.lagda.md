```agda

{-# OPTIONS --safe --erased-cubical #-}

module Trait.HLevel.Base where

open import Prim.Prelude
open import Meta.Cut

is-hlevel : ∀ {ℓ} → Nat → Type ℓ → Type ℓ
is-hlevel zero A = is-contr A
is-hlevel (suc zero) A = is-prop A
is-hlevel (suc (suc n)) A = (x y : A) → is-hlevel (suc n) (x ＝ y)

-- 1lab's definition is to the point
record n-Type ℓ n : Type₊ ℓ where
  no-eta-equality
  field
    ∣_∣ : Type ℓ
    is-tr : is-hlevel n ∣_∣

open n-Type public

is-hom-set : ∀ {o h} {ob : Type o} → (ob → ob → Type h) → Type (o ⊔ h)
is-hom-set H = ∀ x y → is-set (H x y)

is-dprop : ∀ {u v} {A : Type u} → (A → Type v) → Type (u ⊔ v)
is-dprop B = ∀ x → is-prop (B x)

is-grpd : ∀ {ℓ} → Type ℓ → Type ℓ
is-grpd A = (x y : A) → is-set (x ＝ y)

is-prop→PathP : ∀ {ℓ} {A : I → Type ℓ} → ((i : I) → is-prop (A i))
              → ∀ x y → PathP (λ i → A i) x y
is-prop→PathP {A} H x y = to-pathp (H i1 (coe A i1 x) y)

is-prop→SquareP : ∀ {ℓ} {B : I → I → Type ℓ}
                → ((i j : I) → is-prop (B i j))
                → {a : B i0 i0} {b : B i0 i1} {c : B i1 i0} {d : B i1 i1}
                → (p : PathP (λ j → B i0 j) a b)
                → (q : PathP (λ i → B i i0) a c)
                → (r : PathP (λ j → B i1 j) c d)
                → (s : PathP (λ i → B i i1) b d)
                → SquareP B p q r s
is-prop→SquareP {B} bprop {a} p q r s i j =
  let base : (i j : I) → B i j
      base i j = transport (λ k → B (i ∧ k) (j ∧ k)) a
  in hcomp (∂ i ∨ ∂ j) λ where
    k (i = i0) → bprop i0 j (base i0 j) (p j) k 
    k (i = i1) → bprop i1 j (base i1 j) (r j) k
    k (j = i0) → bprop i i0 (base i i0) (q i) k
    k (j = i1) → bprop i i1 (base i i1) (s i) k
    k (k = i0) → base i j

is-contr→is-prop : ∀ {ℓ} {A : Type ℓ} → is-contr A → is-prop A
is-contr→is-prop contr x y i = outS do
  is-contr→extend contr (∂ i) λ where
    (i = i0) → x
    (i = i1) → y

is-contr→is-set : ∀ {ℓ} {A : Type ℓ} → is-contr A → is-set A
is-contr→is-set contr x y p q i j = outS do
  is-contr→extend contr (∂ i ∨ ∂ j) λ where
    (i = i0) → p j
    (i = i1) → q j
    (j = i0) → x
    (j = i1) → y

is-contr→PathP : ∀ {ℓ} {A : I → Type ℓ}
               → ((i : I) → is-contr (A i))
               → (a0 : A i0) (a1 : A i1)
               → PathP A a0 a1
is-contr→PathP contr = is-prop→PathP (λ i → is-contr→is-prop (contr i))

is-prop→is-set : ∀ {ℓ} {A : Type ℓ} → is-prop A → is-set A
is-prop→is-set aprop x = is-contr→is-set (contractible x aprop) x

is-prop-is-prop : ∀ {ℓ} (A : Type ℓ) → is-prop (is-prop A)
is-prop-is-prop A xprop yprop i x y = is-prop→is-set xprop x y (xprop x y) (yprop x y) i

is-hlevel-suc : ∀ {ℓ} {A : Type ℓ} (k : Nat)
              → is-hlevel k A
              → is-hlevel (suc k) A
is-hlevel-suc zero hl = is-contr→is-prop hl
is-hlevel-suc (suc zero) hl = is-prop→is-set hl
is-hlevel-suc (suc (suc k)) hl x y = is-hlevel-suc (suc k) (hl x y)

is-hlevel-add : ∀ {ℓ} {A : Type ℓ} (n k : Nat)
              → is-hlevel k A
              → is-hlevel (n + k) A
is-hlevel-add zero n hl = hl
is-hlevel-add (suc k) n hl = is-hlevel-suc (k + n) (is-hlevel-add k n hl)

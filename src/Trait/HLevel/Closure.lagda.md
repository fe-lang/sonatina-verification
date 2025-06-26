Like Trait.HLevel.Base, the debt for these proofs as well as the
metaprogramming interfaces go to 1lab.

https://1lab.dev/1Lab.HLevel.Closure.html



```agda
{-# OPTIONS --safe --erased-cubical #-}

module Trait.HLevel.Closure where

open import Prim.Base
open import Prim.Cubical
open import Data.Pi
open import Data.Nat.Base
open import Data.Path.Base
open import Data.Path.Square
open import Data.Path.Reasoning
open import Trait.HLevel.Base
open import Trait.Inverse
open import Trait.Equiv

retract→is-contr : ∀ {u v} {A : Type u} {B : Type v} (f : A → B) (g : B → A)
                 → (∀ y → f (g y) ＝ y) → is-contr A → is-contr B
retract→is-contr f g h isC .ctr = f (isC .ctr)
retract→is-contr f g h isC .paths x =
  f (isC .ctr) ＝⟨ ap f (isC .paths _) ⟩
  f (g x)      ＝⟨ h _ ∣
  x               ∎

retract→is-prop : ∀ {u v} {A : Type u} {B : Type v} (f : A → B) (g : B → A)
                → (∀ x → f (g x) ＝ x) → is-prop A → is-prop B
retract→is-prop f g h propA x y =
  x       ＝⟨ sym (h _) ⟩
  f (g x) ＝⟨ ap f (propA _ _) ⟩
  f (g y) ＝⟨ h _ ∣
  y       ∎

retract→is-hlevel : ∀ {u v} {A : Type u} {B : Type v}
                  → (k : Nat) (f : A → B) (g : B → A)
                  → (∀ y → f (g y) ＝ y) → is-hlevel k A → is-hlevel k B
retract→is-hlevel 0 = retract→is-contr
retract→is-hlevel 1 = retract→is-prop
retract→is-hlevel (suc (suc n)) f g h hlevel x y =
  retract→is-hlevel (suc n) sect (ap g) inv (hlevel (g x) (g y)) where
    sect : g x ＝ g y → x ＝ y
    sect path =
      x       ＝⟨ sym (h _) ⟩
      f (g x) ＝⟨ ap f path ⟩
      f (g y) ＝⟨ h _ ∣
      y       ∎

    inv : (p : x ＝ y) → sect (ap g p) ＝ p
    inv path =
      sym (h x) ∙ ap f (ap g path) ∙ h y ＝⟨ ap2 _∙_ refl (sym (homotopy-natural h _)) ⟩
      sym (h x) ∙ h x ∙ path ＝⟨ path-assoc (sym (h x)) (h x) path ⟩
      (sym (h x) ∙ h x) ∙ path ＝⟨ ap2 _∙_ (path-invl (h x)) refl ⟩
      refl ∙ path ＝⟨ path-idnl path ∣
      path ∎

inverse→is-hlevel : ∀ {u v} {A : Type u} {B : Type v} (k : Nat) (f : A → B)
                  → has-inverse f → is-hlevel k A → is-hlevel k B
inverse→is-hlevel k f im = retract→is-hlevel k f g h
  where open has-inverse im renaming (inv to g ; retr to h)

Iso→is-hlevel : ∀ {u v} {A : Type u} {B : Type v} (k : Nat)
              → Iso B A → is-hlevel k A → is-hlevel k B
Iso→is-hlevel n (f , im) = retract→is-hlevel n g f h
  where open has-inverse im renaming (inv to g ; sec to h)

equiv→is-hlevel : ∀ {u v} {A : Type u} {B : Type v} (k : Nat)
                → (f : A → B) → is-equiv f → is-hlevel k A → is-hlevel k B
equiv→is-hlevel k f eqv = inverse→is-hlevel k f (equiv→inverse eqv)

Equiv→is-hlevel : ∀ {u v} {A : Type u} {B : Type v} (k : Nat)
                → (B ≃ A) → is-hlevel k A → is-hlevel k B
Equiv→is-hlevel n f = equiv→is-hlevel n _ (Equiv.inverse f .snd)

Π-is-hlevel : ∀ {u v} {A : Type u} {B : A → Type v}
            → (n : Nat) (Bhl : (x : A) → is-hlevel n (B x))
            → is-hlevel n ((x : A) → B x)
Π-is-hlevel 0 bhl = record
  { paths = λ x i a → bhl _ .paths (x a) i
  }
Π-is-hlevel 1 bhl f g i a = bhl a (f a) (g a) i
Π-is-hlevel (suc (suc n)) bhl f g = retract→is-hlevel (suc n)
  funext happly (λ x → refl)
  (Π-is-hlevel (suc n) λ x → bhl x (f x) (g x))

Π-is-hlevel'
  : ∀ {a b} {A : Type a} {B : A → Type b}
  → (n : Nat) (Bhl : (x : A) → is-hlevel n (B x))
  → is-hlevel n ({x : A} → B x)
Π-is-hlevel' n bhl = retract→is-hlevel n
  (λ f {x} → f x) (λ f x → f) (λ _ → refl)
  (Π-is-hlevel n bhl)

Π-is-hlevel-inst
  : ∀ {a b} {A : Type a} {B : A → Type b}
  → (n : Nat) (Bhl : (x : A) → is-hlevel n (B x))
  → is-hlevel n (⦃ x : A ⦄ → B x)
Π-is-hlevel-inst n bhl = retract→is-hlevel n
  (λ f ⦃ x ⦄ → f x) (λ f x → f ⦃ x ⦄) (λ _ → refl)
  (Π-is-hlevel n bhl)

fun-is-hlevel : ∀ {u v} {A : Type u} {B : Type v}
              → ∀ k → is-hlevel k B → is-hlevel k (A → B)
fun-is-hlevel n hl = Π-is-hlevel n λ _ → hl

Σ-is-hlevel : ∀ {u v} {A : Type u} {B : A → Type v} (k : Nat)
            → is-hlevel k A → (∀ x → is-hlevel k (B x))
            → is-hlevel k (Σ B)
Σ-is-hlevel 0 acontr bcontr .ctr = acontr .ctr , bcontr _ .ctr
Σ-is-hlevel 0 acontr bcontr .paths = λ x → Σ-PathP
    (acontr .paths _)
    (is-prop→PathP (λ _ → is-contr→is-prop (bcontr _)) _ _)
Σ-is-hlevel 1 aprop bprop (a , b) (a' , b') i =
  aprop a a' i , is-prop→PathP (λ i → bprop (aprop a a' i)) b b' i
Σ-is-hlevel {B = B} (suc (suc n)) h1 h2 (x , p) (y , q) =
  inverse→is-hlevel (suc n) _ (Σ-Path-Iso .snd) $
    Σ-is-hlevel (suc n) (h1 x y) λ x → h2 y (subst B x p) q

×-is-hlevel : ∀ {u v} {A : Type u} {B : Type v}
            → ∀ k → is-hlevel k A → is-hlevel k B → is-hlevel k (A × B)
×-is-hlevel n ahl bhl = Σ-is-hlevel n ahl (λ _ → bhl)

opaque
  Lift-is-hlevel : ∀ {u v} {A : Type u} → ∀ n → is-hlevel n A → is-hlevel n (Lift v A)
  Lift-is-hlevel n a-hl = retract→is-hlevel n lift lower (λ _ → refl) a-hl

fibre-is-hlevel : ∀ {u v} {A : Type u} {B : Type v} k → is-hlevel k A → is-hlevel k B
  → (f : A → B) → ∀ b → is-hlevel k (fiber f b)
fibre-is-hlevel {A} {B} n Ah Bh f b = Σ-is-hlevel n Ah λ _ → Path-is-hlevel n Bh

record H-Level {ℓ} (n : Nat) (T : Type ℓ) : Type ℓ where
  constructor hlevel-instance
  field
    has-hlevel : is-hlevel n T

hlevel : ∀ {ℓ} {T : Type ℓ} n ⦃ x : H-Level n T ⦄ → is-hlevel n T
hlevel n ⦃ x ⦄ = H-Level.has-hlevel x

module _ where
  open H-Level
  H-Level-is-prop : ∀ {ℓ} (T : Type ℓ) {k} → is-prop (H-Level k T)
  H-Level-is-prop T {k} x y i .has-hlevel =
    is-hlevel-is-prop T k (x .has-hlevel) (y .has-hlevel) i

basic-instance : ∀ {ℓ} {T : Type ℓ} n → is-hlevel n T → ∀ {k} → H-Level (n + k) T
basic-instance {T = T} n hl {k} =
  subst (λ n → H-Level n T) (+-comm n k) (hlevel-instance (is-hlevel-add k n hl))
  where
    +-comm : ∀ n k → k + n ＝ n + k
    +-comm zero k = go k where
      go : ∀ k → k + 0 ＝ k
      go zero = refl
      go (suc x) = ap suc (go x)
    +-comm (suc n) k = go n k ∙ ap suc (+-comm n k) where
      go : ∀ n k → k + suc n ＝ suc (k + n)
      go n zero = refl
      go n (suc k) = ap suc (go n k)

prop-instance : ∀ {ℓ} {T : Type ℓ} → is-prop T → ∀ {k} → H-Level (suc k) T
prop-instance {T = T} hl = hlevel-instance (is-prop→is-hlevel-suc hl)

instance opaque
  H-Level-Pi
    : ∀ {u v} {T : Type u} {n} {S : T → Type v}
    → ⦃ ∀ {x} → H-Level n (S x) ⦄
    → H-Level n (∀ x → S x)
  H-Level-Pi {n = n} .H-Level.has-hlevel = Π-is-hlevel n λ _ → hlevel n

  H-Level-⊤ : ∀ {n} → H-Level n ⊤
  H-Level-⊤ {n = zero} = hlevel-instance (tt , (λ x i → tt))
  H-Level-⊤ {n = suc n} = prop-instance λ x y i → tt

  H-Level-⊥ : ∀ {n} → H-Level (suc n) ⊥
  H-Level-⊥ {n = n} = prop-instance λ x y → absurd x

  H-Level-Pi'
    : ∀ {u v} {T : Type u} {n} {S : T → Type v}
    → ⦃ ∀ {x} → H-Level n (S x) ⦄
    → H-Level n (∀ {x} → S x)
  H-Level-Pi' {n = n} .H-Level.has-hlevel = Π-is-hlevel' n λ _ → hlevel n

  H-Level-Pi''
    : ∀ {u v} {T : Type u} {n} {S : T → Type v}
    → ⦃ ∀ {x} → H-Level n (S x) ⦄
    → H-Level n (∀ ⦃ x ⦄ → S x)
  H-Level-Pi'' {n = n} .H-Level.has-hlevel = Π-is-hlevel-inst n λ _ → hlevel n

  H-Level-Sigma
    : ∀ {u v} {T : Type u} {n} {S : T → Type v}
    → ⦃ H-Level n T ⦄ → ⦃ ∀ {x} → H-Level n (S x) ⦄
    → H-Level n (Σ S)
  H-Level-Sigma {n = n} .H-Level.has-hlevel =
    Σ-is-hlevel n (hlevel n) λ _ → hlevel n

  H-Level-PathP
    : ∀ {ℓ} {S : I → Type ℓ} {n} ⦃ s : H-Level (suc n) (S i1) ⦄ {x y}
    → H-Level n (PathP S x y)
  H-Level-PathP {S} {n} .H-Level.has-hlevel =
    PathP-is-hlevel-suc S n (hlevel (suc n)) _ _

  H-Level-Lift
    : ∀ {u v} {T : Type u} {n} ⦃ s : H-Level n T ⦄ → H-Level n (Lift v T)
  H-Level-Lift {n = n} .H-Level.has-hlevel = Lift-is-hlevel n (hlevel n)

  H-Level-is-contr : ∀ {n} {ℓ} {T : Type ℓ} → H-Level (suc n) (is-contr T)
  H-Level-is-contr {T} = prop-instance (is-contr-is-prop T)

  H-Level-is-equiv
    : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'} {f : A → B} {n}
    → H-Level (suc n) (is-equiv f)
  H-Level-is-equiv = prop-instance (is-equiv-is-prop _)

positive-hlevel : ∀ {ℓ} (T : Type ℓ) → Nat → Type _
positive-hlevel T n = ∀ {k : Nat} → H-Level (n + k) T
{-# INLINE positive-hlevel #-}

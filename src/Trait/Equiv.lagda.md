```agda

{-# OPTIONS --safe --erased-cubical #-}

module Trait.Equiv where

open import Prim.Prelude
open import Lib.Fiber

open import Data.Path.Type
open import Data.Path.Square
open import Data.Path.Transport

open import Trait.Contr public
open import Trait.Inverse public

infix 4 _≃_

record is-equiv {u v} {A : Type u} {B : Type v} (f : A → B) : Type (u ⊔ v) where
  no-eta-equality
  field
    contr-map : (y : B) → is-contr (fiber f y)

  fun = f

  center : (y : B) → fiber f y
  center y = contr-map y .ctr

  inv : B → A
  inv y = center y .fst

  fibers : {y : B} (fb : fiber f y) → center y ＝ fb
  fibers {y} = contr-map y .paths

  sec : (x : A) → inv (f x) ＝ x
  sec x i = fibers (x , refl) i .fst

  retr :  (y : B) → f (inv y) ＝ y
  retr y = center y .snd

  abstract
    adj : (x : A) → ap f (sec x) ＝ retr (f x)
    adj x = transpose (tri.by-pre _ _ _ (hsym (fp x))) where
      fp : (x : A) → Square (retr (f x)) (ap f (sec x)) (erefl (f x)) (erefl (f x))
      fp x i j = fibers (x , refl) i .snd j

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
           ; inv-adj to eqv-adj⁻¹ )


_≃_ : ∀ {u v} → Type u → Type v → Type (u ⊔ v)
A ≃ B = Σ {A = A → B} is-equiv
{-# BUILTIN EQUIV      _≃_   #-}

Equiv = _≃_

eqvtofun : ∀ {u v} {A : Type u} {B : Type v} → A ≃ B → A → B
eqvtofun e = fst e
{-# BUILTIN EQUIVFUN   eqvtofun  #-}

equiv-proof : ∀ {u v} (T : Type u) (A : Type v) (w : T ≃ A) (a : A)
            → ∀ φ (u : Partial φ (fiber (w .fst) a)) → fiber (w .fst) a [ φ ↦ u ]
equiv-proof {u} {v} T A w a = is-contr→extend (contr-map (w .snd) a)

{-# BUILTIN EQUIVPROOF equiv-proof #-}

ap-coh : ∀ {u} {A : Type u} {x y : A} (p : x ＝ y)
                → ap (λ x → x) p ＝ p
ap-coh = erefl

is-hae : ∀ {u v} {A : Type u} {B : Type v} (f : A → B) → Type (u ⊔ v)
is-hae {A} {B} f = Σ g ∶ (B → A)
                 , Σ s ∶ (∀ x → g (f x) ＝ x)
                 , Σ r ∶ (∀ y → f (g y) ＝ y)
                 , ∀ x → ap f (s x) ＝ r (f x)

hae→equiv : ∀ {u v} {A : Type u} {B : Type v} {f : A → B}
          → is-hae f → is-equiv f
hae→equiv {A} {B} {f} (g , η , ε , α) .contr-map = contr where
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

module Equiv {u v} {A : Type u} {B : Type v} ((f , e) : A ≃ B) where
  private
    module e = is-equiv e

  to = f
  from = e.inv

  inverse : B ≃ A
  inverse = e.inv , hae→equiv (f , e.retr , e.sec , e.inv-adj)

equiv→inverse : ∀ {u v} {A : Type u} {B : Type v} {f : A → B}
           → is-equiv f → has-inverse f
equiv→inverse e .inverse-inv = eqv-inv e
equiv→inverse e .inverse-sec = eqv-sec e
equiv→inverse e .inverse-retr = eqv-retr e

inverse→equiv : ∀ {u v} {A : Type u} {B : Type v} {f : A → B}
           → has-inverse f → is-equiv f
inverse→equiv q .contr-map = inverse→contr-map q  

Iso→Equiv : ∀ {u v} {A : Type u} {B : Type v} (e : Iso A B) → A ≃ B
Iso→Equiv e = e .fst , inverse→equiv (e .snd)

equiv : ∀ {u v} {A : Type u} {B : Type v}
      → (f : A → B) (g : B → A)
      → (∀ x → g (f x) ＝ x)
      → (∀ y → f (g y) ＝ y)
      → is-equiv f
equiv f g s r = inverse→equiv q
  where
    q : has-inverse f
    q .inverse-inv = g
    q .inverse-sec = s
    q .inverse-retr = r

-- Constructor for _≃_
Equiv-intro : ∀ {u v} {A : Type u} {B : Type v}
      → (f : A → B) (g : B → A)
      → (∀ x → g (f x) ＝ x)
      → (∀ y → f (g y) ＝ y)
      → A ≃ B
Equiv-intro f g s r .fst = f
Equiv-intro f g s r .snd = equiv f g s r

Equiv→Iso : ∀ {u v} {A : Type u} {B : Type v} → A ≃ B → Iso A B
Equiv→Iso e = e .fst , equiv→inverse (e .snd)

transport-is-equiv : ∀ {ℓ} (A : I → Type ℓ) → is-equiv (transport (λ i → A i))
transport-is-equiv A = hae→equiv (g , η , ε , α)
  where
    f = transport (λ i → A i)
    g = transport (λ i → A (~ i))
    η = transport.unit A
    ε = transport.counit A
    α = transport.adj A

pathtoeqv : ∀ {u} {A B : Type u} → A ＝ B → A ≃ B
pathtoeqv P = transport P , transport-is-equiv λ i → P i

id-equiv : ∀ {u} {A : Type u} → is-equiv {A = A} (λ x → x)
id-equiv .contr-map x .ctr .fst = x
id-equiv .contr-map x .ctr .snd = refl
id-equiv .contr-map x .paths (y , p) i  = p (~ i) , λ j → p (~ i ∨ j)

eqv-refl : ∀ {u} (A : Type u) → A ≃ A
eqv-refl A .fst = id
eqv-refl A .snd = id-equiv

eqv-sym : ∀ {u v} {A : Type u} {B : Type v} → A ≃ B → B ≃ A
eqv-sym = Equiv.inverse

-- This proof follows the one presented in the agda-cubical library:
-- https://agda.github.io/cubical/Cubical.Foundations.Equiv.html#3750
eqv-concat : ∀ {u v w} {A : Type u} {B : Type v} {C : Type w}
           → A ≃ B → B ≃ C → A ≃ C
eqv-concat e d .fst = Equiv.to d ∘ Equiv.to e
eqv-concat {A} e d .snd .contr-map z = contr where
  module e = is-equiv (e .snd)
  module d = is-equiv (d .snd)
  contraction : (y : fiber (d .fst) z) → contr-map (d .snd) z .ctr ＝ y
  contraction = d .snd .contr-map z .paths

  sec-filler : (x : A) (p : d.fun (e.fun x) ＝ z)
             → Square refl _ (e.sec x) _
  sec-filler x p =
    path-filler refl (ap (e.inv ∘ fst) (contraction (_ , p))) (e.sec x)

  contr : is-contr (fiber (d.fun ∘ e.fun) z)
  contr .ctr .fst = e.inv (d.inv z)
  contr .ctr .snd = ap d.fun (e.retr (d.inv z)) ∙ d.retr z
  contr .paths (x , p) i .fst = sec-filler x p i i1
  contr .paths (x , p) i .snd j = hcomp (i ∨  ∂ j) λ where
    k (i = i1) → f-square k
    k (j = i0) → d.fun (e.fun (sec-filler x p i k))
    k (j = i1) → contraction (e.fun x , p) i .snd k
    k (k = i0) → d.fun (e.retr (contraction (e.fun x , p) i .fst) j)
      where
      f-square : d .fst (e.center (e.fun x) .snd j) ＝ p j
      f-square k = hcomp (∂ j ∨ ∂ k) λ where
        l (j = i0) → d.fun (e.fun (e.sec x k))
        l (j = i1) → p (k ∧ l)
        l (k = i0) → d.fun (e.retr (e.fun x) j)
        l (k = i1) → p (j ∧ l)
        l (l = i0) → d.fun (e.fibers (x , refl) k .snd j)

module _ {u v w} {A : Type u} {B : Type v} {C : Type w} {h : A → B}
  (e : is-equiv h)
  where
  private module e = is-equiv e
  precomp-is-equiv : is-equiv (λ (k : B → C) → k ∘ h)
  precomp-is-equiv = equiv (λ k → k ∘ h) (_∘ e.inv)
    (λ k → ap (k ∘_) (funext $ e.retr))
    (λ k → ap (k ∘_) (funext $ e.sec))

  postcomp-is-equiv : is-equiv (λ (k : C → A) → h ∘ k)
  postcomp-is-equiv = equiv (λ k → h ∘ k) (e.inv ∘_)
    (λ k → ap (_∘ k) (funext $ e.sec))
    (λ k → ap (_∘ k) (funext $ e.retr))
